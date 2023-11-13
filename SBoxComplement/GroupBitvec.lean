-- This file's goal is to show that bitvectors are a additive group

import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas

open Vector
open Nat

lemma Bitvec.eq : ∀ (a b : Bitvec n), a.val = b.val ↔ a = b  := by
  intro a b
  exact Subtype.ext_iff_val.symm

example  (va : List Bool): List.length va = @List.length Bool [] → va = [] := by apply?

lemma Bitvec.eq2 : ∀ (a b : Bitvec n), a = b ↔ a.toNat = b.toNat := by
  intro a b
  apply Iff.intro
  · -- ->
    intro heq
    rw [heq]
  · -- <-
    intro heq
    cases' a with va pa
    cases' b with vb pb
    simp [bitsToNat_toList] at heq
    unfold bitsToNat at heq
    simp [← Bitvec.eq]
    cases va with
    | nil =>
      rw [← pb] at pa
      rw [List.length_nil] at pa
      exact (List.length_eq_zero.mp pa.symm).symm
    | cons head tail =>
      rw [List.foldl] at heq
      simp [addLsb] at heq
      cases head with
      | false =>
        simp at heq
        cases vb with
        | nil =>
          rw [← pb] at pa
          rw [List.length_nil] at pa
          exact List.length_eq_zero.mp pa
        | cons headb tailb =>
          cases headb with
          | false => sorry
          | true => sorry

      | true =>
        sorry

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
#eval tail (⟨[true, false], by simp [*]⟩ : Bitvec 2)

lemma Bitvec.tail_val_eq_val : ∀ (b : Bitvec n) (a : Bool), b =
        (tail (⟨a :: b.val, by simp [*] ⟩ : Bitvec (n + 1))) := by
  intro b
  simp [← Bitvec.eq]

-- lemma test: ∀ (b : Bitvec n) (a : Bool), b =
--         (tail (⟨a :: b.val, by simp [*] ⟩ : Bitvec (n + 1))) := by

--         sorry

#check ofNat_succ


lemma test: ∀ (v : List Bool), List.length v = 0 → v = [] := by exact?

lemma Bitvec_add : ∀ (a b : Bitvec n), (a + b).toNat = (a.toNat + b.toNat) % 2^n := by
  intro a b
  induction n with
  | zero =>
    simp [Nat.mod_one]
    sorry
  | succ n ih =>
    simp [Bitvec.toNat_append, ih, bits_toNat_decide, mod_pow_succ, Nat.mul_comm]
    sorry


lemma Bitvec.add_assoc : ∀ (a b c : Bitvec n), Bitvec.add a (Bitvec.add b c) = Bitvec.add (Bitvec.add a b) c := by
  intro a b c
  simp [Bitvec.eq2]


  rw [Bitvec.add, tail]
  match adc a (Bitvec.add b c) false with
  | { val := [], property := h } =>
    contradiction
  | { val := head :: v, property := h } =>
    simp
    rw [Bitvec.add, tail]
    match adc (Bitvec.add a b) c false with
    | { val := [], property := h2 } =>
      contradiction
    | { val := head2 :: v2, property := h2 } =>
      simp
      rw [← Bitvec.eq]
      simp
      induction n with
      | zero =>
        simp at h
        have h' := List.length_eq_zero.mp h
        simp at h2
        have h2' := List.length_eq_zero.mp h2
        rw [h', h2']
      | succ n ih =>

        sorry
  -- rw [← Bitvec.eq]
  -- induction n with
  -- | zero => simp
  -- | succ n ih =>
  --   rw [← Bitvec.eq]
  --   -- let bool := head a
  --   -- cases' a with va pa
  --   -- cases' b with vb pb
  --   -- cases' c with vc pc
  --   -- specialize ih (tail a) (tail b) (tail c)
  --   rw [Bitvec.tail_val_eq_val a true]
  --   generalize tail { val := true :: a.val, property := (_ : succ (List.length a.val) = succ n + 1) } = a'
  --   rw [Bitvec.tail_val_eq_val b true]
  --   rw [Bitvec.tail_val_eq_val c true]
  --   -- cases' a with va pa
  --   -- cases' b with vb pb
  --   -- cases' c with vc pc
  --   -- rw [← Bitvec.eq] at ih





    -- sorry


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
