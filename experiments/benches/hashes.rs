#![feature(const_generics)]
#![feature(const_evaluatable_checked)]
#![allow(incomplete_features)]
use std::{collections::HashMap, hash::BuildHasher, iter::FromIterator, ops::Range};

use criterion::{
    black_box, criterion_group, criterion_main, measurement::WallTime, Bencher, BenchmarkGroup,
    Criterion,
};
use rand::{distributions::Alphanumeric, prelude::Rng, prelude::StdRng, thread_rng, SeedableRng};

use ahash::RandomState as AHashBuilder;
use fnv::FnvHashMap;

const N_OBJECTS: usize = 10_000;

#[derive(Clone)]
struct Entry<K, V>(K, V);

fn generate_arrays<const N_SAMPLES: usize, const N_KEYS: usize>(
    state: u64,
    key_range: Range<u8>,
) -> (Vec<Vec<Entry<String, usize>>>, Vec<String>) {
    let mut rng = StdRng::seed_from_u64(state);
    let mut output = vec![vec![Entry(String::new(), 0); N_KEYS]; N_SAMPLES];
    let mut all_keys = vec![String::new(); N_KEYS * N_SAMPLES];

    for i in 0..N_SAMPLES {
        for j in 0..N_KEYS {
            let key_size = rng.gen_range(key_range.clone());
            let key = (&mut rng)
                .sample_iter(&Alphanumeric)
                .take(key_size as usize)
                .collect::<Vec<u8>>();
            output[i][j] = Entry(String::from_utf8(key).unwrap(), rng.gen());
            all_keys[i * N_KEYS + j] = output[i][j].0.clone();
        }
    }

    (output, all_keys)
}

fn vec_to_map<H>(v: &[Vec<Entry<String, usize>>]) -> Vec<H>
where
    H: FromIterator<(String, usize)>,
{
    let mut out = Vec::with_capacity(v.len());

    for obj in v {
        out.push(obj.clone().into_iter().map(|k| (k.0, k.1)).collect());
    }

    out
}

fn run_linear_search(b: &mut Bencher, data: &[Vec<Entry<String, usize>>], keys: &[String]) {
    let mut rng = thread_rng();
    let n_objects = data.len();
    let n_keys = keys.len();
    b.iter(|| {
        let mut hits = 0;

        let key = &keys[rng.gen_range(0..n_keys)];
        let obj = &data[rng.gen_range(0..n_objects)];

        for name in obj {
            if &name.0 == key {
                hits += 1;
            }
        }

        black_box(hits)
    });
}

fn run_hashmap_search<H: BuildHasher>(
    b: &mut Bencher,
    data: &[HashMap<String, usize, H>],
    keys: &[String],
) {
    let mut rng = thread_rng();
    let n_objects = data.len();
    let n_keys = keys.len();
    b.iter(|| {
        let mut hits = 0;

        let key = &keys[rng.gen_range(0..n_keys)];
        let obj = &data[rng.gen_range(0..n_objects)];

        if obj.get(key).is_some() {
            hits += 1;
        }

        black_box(hits)
    });
}

fn bench_for_obj_size<const SIZE: usize>(group: &mut BenchmarkGroup<WallTime>, state: u64) {
    let (data, keys) = generate_arrays::<N_OBJECTS, SIZE>(state, 1..11);
    group.bench_with_input(
        format!(
            "<linear search ({} elements, key size range = 1..=10)>",
            SIZE
        ),
        &(&data, &keys),
        move |b, (data, keys)| run_linear_search(b, data, keys),
    );

    let data_map = vec_to_map::<HashMap<_, _>>(&data);
    group.bench_with_input(
        format!(
            "<siphash13 hashmap search ({} elements, key size range = 1..=10)>",
            SIZE
        ),
        &(&data_map, &keys),
        move |b, (data, keys)| run_hashmap_search(b, data, keys),
    );

    let data_map = vec_to_map::<FnvHashMap<_, _>>(&data);
    group.bench_with_input(
        format!(
            "<fnv hashmap search ({} elements, key size range = 1..=10)>",
            SIZE
        ),
        &(&data_map, &keys),
        move |b, (data, keys)| run_hashmap_search(b, data, keys),
    );

    let data_map = vec_to_map::<HashMap<_, _, AHashBuilder>>(&data);
    group.bench_with_input(
        format!(
            "<ahash hashmap search ({} elements, key size range = 1..=10)>",
            SIZE
        ),
        &(&data_map, &keys),
        move |b, (data, keys)| run_hashmap_search(b, data, keys),
    );
}

fn bench_lookups(c: &mut Criterion) {
    let state = dbg!(std::time::SystemTime::now()
        .duration_since(std::time::SystemTime::UNIX_EPOCH)
        .unwrap()
        .as_secs());

    let mut group = c.benchmark_group("field_lookups");
    bench_for_obj_size::<5>(&mut group, state);
    bench_for_obj_size::<10>(&mut group, state);
    bench_for_obj_size::<20>(&mut group, state);
    bench_for_obj_size::<30>(&mut group, state);
    bench_for_obj_size::<100>(&mut group, state);
}

criterion_group!(benches, bench_lookups);
criterion_main!(benches);
