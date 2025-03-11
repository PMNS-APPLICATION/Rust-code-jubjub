use std::time::{Duration, Instant};

use ff::Field;
use group::{Curve, Group};
use jubjublib::{from_int_to_pmns, from_pmns_to_int, AffinePointPmns, ExtendedPoint, Fr};
use rand::rngs::OsRng;

fn main() {
    let mut rng = OsRng;
    let mut time = Duration::ZERO;
    let mut time1 = Duration::ZERO;

    let mut idx = 0;

    while idx < 10000 {
        /*
        Partie création du point et du scalaire.
        */
        let sc = Fr::random(&mut rng);
        let generator = ExtendedPoint::generator();
        let point = (generator * sc).to_affine();

        let u_pmns = from_int_to_pmns(point.get_u());
        let v_pmns = from_int_to_pmns(point.get_v());

        let pmns_point = AffinePointPmns::from_raw_unchecked(u_pmns, v_pmns);

        let scalar = Fr::random(&mut rng);

        /*
        Partie mutliplication et prise de mesure utilisant l'algorithmie classique.
        */

        let point_niels = point.to_niels();

        let start = Instant::now();
        let result = point_niels * scalar;
        let duration = start.elapsed();
        time += duration;

        let new_point = result.to_affine();

        /*
        Vérification que le résultat est sur la courbe.
        */
        if !new_point.is_on_curve_vartime() {
            println!("❌ The resulting point from the classic algorithmic is NOT on the curve!");
            idx += 10000;
        }

        /*
        Partie où on fait la multiplication mais en utilisant l'arithmétique pmns.
        */

        let pmns_point_niels = pmns_point.to_niels();

        let start1 = Instant::now();
        let pmns_result = pmns_point_niels * scalar;
        let duration1 = start1.elapsed();
        time1 += duration1;

        let ue = from_pmns_to_int(&pmns_result.get_u());
        let ve = from_pmns_to_int(&pmns_result.get_v());
        let ze = from_pmns_to_int(&pmns_result.get_z());
        let t1e = from_pmns_to_int(&pmns_result.get_t1());
        let t2e = from_pmns_to_int(&pmns_result.get_t2());

        let ext_after_pmns = ExtendedPoint::from_raw_unchecked(ue, ve, ze, t1e, t2e);
        let new_pmns_point = ext_after_pmns.to_affine();

        /*
        Vérification que le résultat est sur la courbe.
        */
        if !new_pmns_point.is_on_curve_vartime() {
            println!("❌ The resulting point from the pmns algorithmic is NOT on the curve!");
            idx += 10000;
        }

        if new_point != new_pmns_point {
            idx += 10000;
            println!("NOT THE SAME RESULT !");
            println!("The point after classic algorithmic:\n{:?}", new_point);
            println!("The point after pmns algorithmic:\n{:?}", new_pmns_point);
        }

        idx += 1;
    }

    println!(
        "Time elapsed for Full Scalar Multiplication with classical algorithmic in ms: {:?}",
        time / 10000
    );
    println!(
        "Time elapsed for Full Scalar Multiplication with pmns algorithmic in ms: {:?}",
        time1 / 10000
    );
}
