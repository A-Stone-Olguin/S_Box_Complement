import Mathlib.Data.Bitvec.Defs

-- #eval (7 : Bitvec 3)
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
#eval HammingWeight (Bitvec.one 3) -- 2

-- #check cases

lemma n_const_hamming_weight : ∀ {n : ℕ} (x : Bitvec n), ∃ (y : Bitvec n), HammingWeight (x + y) = n := by
  intro n x
  let y := -(x + Bitvec.one n)
  use y
  have h : x + -(x + Bitvec.one n ) = -(Bitvec.one n) := by
    sorry
  simp [y]
  have h_calc : (-(Bitvec.one n)).toNat = 2^n - 1 := by
    sorry


  induction n with
  | zero =>
    have h : x + -(x + Bitvec.one zero ) = Bitvec.one zero := by simp
    rw [h]
    rfl
  | succ n ih =>

    sorry
