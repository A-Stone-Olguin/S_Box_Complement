import Mathlib.Data.Bitvec.Defs

#eval (7 : Bitvec 3)

instance (n : ℕ) : OfNat (Bitvec n) x where
  ofNat := Bitvec.ofNat n x

#eval (7 : Bitvec 3)
#eval Bitvec.ofNat 3 7
