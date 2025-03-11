use std::arch::asm;

use ff::Field;
use jubjublib::{from_int_to_pmns, from_pmns_to_int, mult_mod_poly, Fq};
use rand::rngs::OsRng;

#[inline(always)]
fn rdtsc() -> u64 {
    let hi: u32;
    let lo: u32;
    unsafe {
        asm!("rdtsc", out("eax") lo, out("edx") hi);
    }
    ((hi as u64) << 32) | (lo as u64)
}

fn main() {
    let mut rng = OsRng;
    let mut cpu = 0;
    let mut cpu1 = 0;

    let mut idx = 0;

    while idx < 10000 {
        /*
        Partie création du point et du scalaire.
        */
        let sc1 = Fq::random(&mut rng);
        let sc2 = Fq::random(&mut rng);

        let sc1_pmns = from_int_to_pmns(sc1);
        let sc2_pmns = from_int_to_pmns(sc2);

        /*
        Partie mutliplication et prise de mesure utilisant l'algorithmie classique.
        */
        let start = rdtsc();
        let result = sc1 * sc2;
        let end = rdtsc();
        cpu = cpu + (end - start);

        /*
        Partie où on fait la multiplication mais en utilisant l'arithmétique pmns.
        */
        let start1 = rdtsc();
        let pmns_result = mult_mod_poly(&sc1_pmns, &sc2_pmns);
        let end1 = rdtsc();
        cpu1 = cpu1 + (end1 - start1);

        /*
        Vérification que le résultat est le même.
        */
        let result_pmns_transform = from_pmns_to_int(&pmns_result);

        if result != result_pmns_transform {
            idx += 10000;
            println!("NOT THE SAME RESULT !");
            println!("The point after classic algorithmic:\n{:?}", result);
            println!(
                "The point after pmns algorithmic:\n{:?}",
                result_pmns_transform
            );
        }

        idx += 1;
    }

    println!(
        "Number of cycle for Modular Multiplication with classic algorithmic: {:?}",
        cpu / 10000
    );
    println!(
        "Number of cycle for Modular Multiplication with pmns algorithmic: {:?}",
        cpu1 / 10000
    );
}
