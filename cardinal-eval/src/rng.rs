//! Reproducible orders (§1.4): one RNG per (seed, benchmark, target,
//! trial), the same whatever else a run does.

use rand::SeedableRng;
use rand::seq::SliceRandom;
use rand_chacha::ChaCha8Rng;

/// FNV-1a over `parts`, each ended by a 0 byte: stable across platforms
/// and Rust releases, unlike `std`'s hashers.
pub fn stable_hash(parts: &[&[u8]]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for p in parts {
        for &b in p.iter().chain(&[0u8]) {
            h ^= u64::from(b);
            h = h.wrapping_mul(0x0100_0000_01b3);
        }
    }
    h
}

/// The RNG of (seed, bench, target, trial).
pub fn rng(seed: u64, bench: &str, target: &str, trial: u32) -> ChaCha8Rng {
    ChaCha8Rng::seed_from_u64(stable_hash(&[&seed.to_le_bytes(), bench.as_bytes(), target.as_bytes(), &trial.to_le_bytes()]))
}

/// `items` permuted by the RNG of (seed, bench, target, trial).
pub fn permuted<T: Clone>(items: &[T], seed: u64, bench: &str, target: &str, trial: u32) -> Vec<T> {
    let mut out = items.to_vec();
    out.shuffle(&mut rng(seed, bench, target, trial));
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn orders_are_reproducible_and_differ_by_trial() {
        let xs: Vec<u32> = (0..20).collect();
        assert_eq!(permuted(&xs, 1, "tpch", "q01", 0), permuted(&xs, 1, "tpch", "q01", 0));
        assert_ne!(permuted(&xs, 1, "tpch", "q01", 0), permuted(&xs, 1, "tpch", "q01", 1));
        assert_ne!(permuted(&xs, 1, "tpch", "q01", 0), permuted(&xs, 1, "tpch", "q02", 0));
        // Pinned, so a change of hash or RNG shows.
        assert_eq!(stable_hash(&[b"a"]), 0x089b_e207_b544_f1e4);
    }
}
