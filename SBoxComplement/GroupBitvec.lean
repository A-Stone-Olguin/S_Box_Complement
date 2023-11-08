-- This file's goal is to show that bitvectors are a additive group

import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas

open Vector
open Nat

lemma Bitvec.eq : ∀ (a b : Bitvec n), a.val = b.val ↔ a = b  := by
  intro a b
  exact Subtype.ext_iff_val.symm

#check Subtype.ext_val
#eval (Bitvec.ofNat 3 3).val
#eval (tail (Bitvec.ofNat 4 3)).val
#eval tail (Bitvec.ofNat 4 9)
#eval (Bitvec.ofNat 3 9)
#check Vector.tail_val
#check List.mapAccumr
#check Vector.tail_nil
#check Vector.append

#check List.length_append
-- def Vector.append' {n m : Nat} : Vector α n → Vector α m → Vector α (n + m)
--   | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by simp [*]⟩

-- def Bitvec.append' {m n} : Bitvec m → Bitvec n → Bitvec (m + n) :=
--   Vector.append

lemma Bitvec.tail_val_eq_val : ∀ (b : Bitvec n) , b =
          tail ⟨a :: b.val, --List.length (a :: b.val) = n + 1
          by
          have h := b.property
          have h_done : List.length (a :: b.val) = n + 1 := by
            simp
          exact h_done
          ⟩ := by
  intro b
  induction n with
  | zero => sorry
  | succ n ih =>
    sorry


lemma Bitvec.add_assoc : ∀ (a b c : Bitvec n), Bitvec.add a (Bitvec.add b c) = Bitvec.add (Bitvec.add a b) c := by
  intro a b c
  induction a
  -- rw [← Bitvec.eq]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Bitvec.eq]

    cases' a with va pa
    cases' b with vb pb
    cases' c with vc pc
    simp [Bitvec.add, adc, mapAccumr₂]


    sorry

  -- simp [Bitvec.add, List.tail]
  -- match (adc { val := va, property := pa }
  --            (tail (adc { val := vb, property := pb }
  --                       { val := vc, property := pc } false))
  --       false).val with
  -- | [] =>  match (adc (tail (adc { val := va, property := pa }
  --                                { val := vb, property := pb } false))
  --                     { val := vc, property := pc } false).val with
  --         | [] => rfl
  --         | head :: as => cases as with
  --                       | nil => rfl
  --                       | cons head tail =>
  -- | head :: as => sorry

  -- simp [Bitvec.add, tail]
  -- split
  -- split
  -- rfl
  -- contradiction
  -- split
  -- contradiction
  -- split at *
  -- split at *
  -- simp [*] at *

  sorry

-- lemma Bitvec.add_assoc : ∀ (a b c : Bitvec n), a + b + c = a + (b + c) := by
--   intro a b c
--   simp [Bitvec.h_add_zero]
--   rw [← Bitvec.eq]
--   -- apply Bitvec.ext
--   cases' a with va pa
--   cases' b with vb pb
--   cases' c with vc pc



--   induction n with
--   | zero => simp
--   | succ n ih =>
--     specialize ih (tail a) (tail b) (tail c)

--     cases' a with va pa
--     cases' b with vb pb
--     cases' c with vc pc
--     apply Subtype.ext_val

--     sorry


instance (n : ℕ): AddGroup (Bitvec n) where
  add := Bitvec.add
  add_assoc := sorry
  zero := Bitvec.zero n
  zero_add := sorry
  add_zero := sorry
  nsmul := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  neg := Bitvec.neg
  sub := Bitvec.sub
  sub_eq_add_neg := sorry
  zsmul := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  add_left_neg := sorry
