import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas
import Mathlib.Tactic

open Nat
open Vector

instance (n : ℕ) : OfNat (Bitvec n) x where
  ofNat := Bitvec.ofNat n x

#eval (7 : Bitvec 3)
#eval Bitvec.ofNat 3 7


def HammingWeight: ∀ {n : ℕ}, Bitvec n → ℕ
  | 0, _ => 0
  | succ _, x =>
    match (head x) with
    | true => 1 + HammingWeight (tail x)
    | false => 0 + HammingWeight (tail x)

#eval HammingWeight (4 : Bitvec 3) -- 1
#eval HammingWeight (7 : Bitvec 3) -- 3
#eval HammingWeight ((7 : Bitvec 3) + (4 : Bitvec 3)) -- 2
#eval HammingWeight (-Bitvec.one 3) -- 3 (-1 = 7 mod 2^3)

-- #check cases
#check Bitvec.instAddBitvec


example : ∀ (n : ℕ), 2 ^(n+1) = 2 * 2^n := by apply?

def neg_one : ∀ n : ℕ, Bitvec n
  | 0 => nil
  | succ n =>  replicate (succ n) true

-- lemma append_true_succ_n : ∀ {n : ℕ}, true ::ᵥ -Bitvec.one n = -Bitvec.one (succ n) := by
--   intro n
--   induction n with
--   | zero => rfl
--   | succ n ih =>
--     rw [← ih]


--     sorry

-- lemma pos_n_neg_one_all_ones : ∀ {n : ℕ}, -Bitvec.one n = (replicate n true) := by
--   intro n
--   induction n with
--   | zero => rfl
--   | succ n ih =>
--     rw [replicate_succ true]

--     sorry

lemma neg_one_eq_neg_bitvec_one : ∀ {n : ℕ}, neg_one n = -Bitvec.one n := by
  intro n
  -- ext h
  induction n with
  | zero => rfl
  | succ n ih =>
    sorry

lemma all_ones_hamming_weight_eq_n : ∀ {n : ℕ }, HammingWeight (replicate n true) = n :=  by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [replicate_succ true]
    unfold HammingWeight
    simp
    rw [ih]
    exact one_add n

lemma neg_one_hamming_weight_eq_n : ∀ {n : ℕ}, HammingWeight (-Bitvec.one n) = n := by
  intro n
  rw [← neg_one_eq_neg_bitvec_one]
  unfold HammingWeight
  cases n with
  | zero => rfl
  | succ n =>
    rw [neg_one]
    simp
    rw [@all_ones_hamming_weight_eq_n n]
    exact one_add n

#check (7 : Bitvec 3).toFin

lemma neg_one_eq_two_pow_n_sub_one : ∀ {n : ℕ}, (-Bitvec.one n).toNat = 2^n - 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Bitvec.bitsToNat_toList, Vector.toList_singleton, Vector.head_cons]
    unfold Bitvec.bitsToNat Bitvec.addLsb List.foldl

  -- unfold bitsToNat addLsb List.foldl
    sorry


lemma const_hamming_weight_n : ∀ {n : ℕ} (x : Bitvec n), ∃ (y : Bitvec n), HammingWeight (x + y) = n := by
  intro n x
  let y := -(x + Bitvec.one n)
  use y
  have h : x + -(x + Bitvec.one n ) = -(Bitvec.one n) := by
    have h1 : -(x + Bitvec.one n) = -x - Bitvec.one n := by sorry
    rw [h1]

    sorry
  simp [y]
  rw [h]
  exact neg_one_hamming_weight_eq_n
