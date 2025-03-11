use std::time::{Duration, Instant};

use ff::Field;
use jubjublib::{
    from_int_to_pmns, from_pmns_to_int, mult_mod_poly, Fq,
};
use rand::rngs::OsRng;

fn main() {
    let mut rng = OsRng;
    let mut time = Duration::ZERO;
    let mut time1 = Duration::ZERO;

    let mut idx = 0;

    while idx < 10000 {
        /*
        Partie création du point dans Fq.
        */
        let sc1 = Fq::random(&mut rng);
        let sc2 = Fq::random(&mut rng);

        let sc1_pmns = from_int_to_pmns(sc1);
        let sc2_pmns = from_int_to_pmns(sc2);

        /*
        Partie mutliplication et prise de mesure utilisant l'algorithmie classique.
        */
        let start = Instant::now();
        let result = sc1 * sc2;
        let duration = start.elapsed();
        time += duration;

        /*
        Partie où on fait la multiplication mais en utilisant l'arithmétique pmns.
        */
        let start1 = Instant::now();
        let pmns_result = mult_mod_poly(&sc1_pmns, &sc2_pmns);
        let duration1 = start1.elapsed();
        time1 += duration1;

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
        "Time elapsed for Modular Multiplication with classic algorithmic in ms: {:?}",
        time / 10000
    );
    println!(
        "Time elapsed for Modular Multiplication with pmns algorithmic in ms: {:?}",
        time1 / 10000
    );
}
