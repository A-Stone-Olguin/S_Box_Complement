import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas
import Mathlib.Tactic

-- import SBoxComplement.GroupBitvec

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
#eval HammingWeight (-Bitvec.one 3) -- 3 (-1 = 7 mod 2^3 = 111₂)

def HammingDistance : ∀ {n : ℕ}, Bitvec n → Bitvec n → ℕ :=
  λ a b => HammingWeight (Bitvec.xor a b)
#eval HammingDistance (4 : Bitvec 3) (7 : Bitvec 3) -- 100 ⊕ 111 = 011, 2 HD

def Vector.modifyNth {α: Type} (n : ℕ) (f : α → α): ℕ → Vector α n → Vector α n:=
  λ nth v => ⟨List.modifyNth f nth v.val, by simp [*]⟩

-- Modifies the nth element of a bitvector
def Bitvec.modifyNth (n : ℕ) (f : Bool → Bool): ℕ → Bitvec n → Bitvec n :=
  λ nth b => Vector.modifyNth n f nth b

-- Flips the Bitvector's values at each specified place in the list
def Bitvec.flip : ∀ {n : ℕ}, (List ℕ) × (Bitvec n) → Bitvec n
  | _, ([], b) => b
  | n, (a :: as, b) => Bitvec.flip (as, Bitvec.modifyNth n Bool.not a b)
#eval (7 : Bitvec 3)                          --111
#eval Bitvec.flip ([0, 2], (7 : Bitvec 3))    --010

def first_n_nats : ℕ → List ℕ
  | 0 => []
  | n + 1 => (n :: (first_n_nats n).reverse).reverse
#eval first_n_nats 5

def first_n_even_nats : ℕ → List ℕ :=
  λ n => List.map (λ (x : Nat) => 2 * x) (first_n_nats n)
#eval first_n_even_nats 4

def flipped_complement : Bitvec n → ℕ → Bitvec n :=
  λ b hw => Bitvec.flip (List.diff (first_n_nats n) (first_n_even_nats (n-hw)), b)
#eval (32 : Bitvec 8)                             --00100000
#eval flipped_complement (32 : Bitvec 8) 7        --01011111



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

lemma const_hamming_weight_n : ∀ {n : ℕ} (x : Bitvec n), ∃ (y : Bitvec n), HammingWeight (x + y) = n := by
  intro n x
  let y := -x + replicate n true
  use -x + replicate n true
  have h : x + (-x + replicate n true) = replicate n true := by
    have h_assoc : x + (-x + replicate n true) = x + -x + replicate n true := by sorry
    rw [h_assoc]
    have h_inv : x + -x = Bitvec.zero n := by sorry
    rw [h_inv]
    have h_add_zero : Bitvec.zero n + replicate n true = replicate n true := by sorry
    rw [h_add_zero]
  rw [h]
  exact all_ones_hamming_weight_eq_n
