import Mathlib.Tactic
import AaBeta

namespace Trial123

#check Group

structure Subgroup (M : Type*) [Mul M] [Group M] where
  carrier : Set M
  mul_mem {a b : M} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  inv_mem {a : M} : a ∈ carrier → a⁻¹ ∈ carrier

/- In this section, I create a type X, consisting of a single element e.
I prove that X is a group, and that X ≤ X -/
inductive X : Type
  | e : X

def mul : X → X → X := fun _ _ => X.e

def inv : X → X := fun _ => X.e

instance : Mul X where
  mul := mul

instance : One X where
  one := X.e

instance : Inv X where
  inv := inv

lemma mul_eq_e (a b : X) : a * b = X.e := by
  simp

example (a b c : X) :  a * b * c = a * (b * c) := by
  simp

instance : Group X where
  mul_assoc := by simp
  one_mul := by simp
  mul_one := by simp
  mul_left_inv := by simp

def c : Set X := fun _ => True

def X1 : Subgroup X where
  carrier := c
  mul_mem := by simp
  inv_mem := by simp


--instance : Group X := by

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  by apply And.intro
     exact hp
     apply And.intro
     exact hq
     exact hp
