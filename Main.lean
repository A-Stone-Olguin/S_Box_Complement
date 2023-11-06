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
