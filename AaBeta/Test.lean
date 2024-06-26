import Mathlib.Tactic

namespace My

class Magma (G : Type*) where
  protected op : G → G → G

attribute [always_inline] Magma.op

infixl:74 " ◆ " => Magma.op  -- \di


class Semigroup (G : Type*) extends Magma G where
  protected assoc : ∀ (a b c : G), (a ◆ b) ◆ c = a ◆ (b ◆ c)

theorem assoc {G : Type*} [Semigroup G] (a b c : G) : (a ◆ b) ◆ c = a ◆ (b ◆ c) :=
  Semigroup.assoc a b c


class Monoid (G : Type*) extends Semigroup G where
  protected id : G
  protected hid : ∀ (a : G), id ◆ a = a ∧ a ◆ id = a

notation:500 "𝕖" => Monoid.id  -- \bbe

theorem id_left {G : Type*} [Monoid G] (a : G) : 𝕖 ◆ a = a := And.left <| Monoid.hid a

theorem id_right {G : Type*} [Monoid G] (a : G) : a ◆ 𝕖 = a := And.right $ Monoid.hid a


class CommutativeMonoid (G : Type*) extends Monoid G where
  protected comm : ∀ (a b : G), a ◆ b = b ◆ a

theorem comm {G : Type*} [CommutativeMonoid G] (a b : G) : a ◆ b = b ◆ a :=
  CommutativeMonoid.comm a b


class Group (G : Type*) extends Monoid G where
  protected inv : G → G
  protected inv_left : ∀ (a : G), (inv a) ◆ a = 𝕖

postfix:max "⁻¹" => Group.inv  -- \dag

theorem inv_left {G : Type*} [Group G] (a : G) : a⁻¹ ◆ a = 𝕖 := Group.inv_left a

theorem inv_right {G : Type*} [Group G] (a : G) : a ◆ a⁻¹ = 𝕖 := sorry -- TODO: homework

class AbelianGroup (G : Type*) extends Group G, CommutativeMonoid G


/- Down the line -/

instance [Mul G] : Magma G where
  op := HMul.hMul

class MulSemigroup (G : Type*) extends Mul G where
  protected assoc : ∀ (a b c : G), (a * b) * c = a * (b * c)

instance [MulSemigroup G] : Semigroup G where
  assoc := MulSemigroup.assoc

theorem mul_assoc {G : Type*} [MulSemigroup G] (a b c : G) : (a * b) * c = a * (b * c) :=
  assoc a b c

/- ... -/

instance [Add G] : Magma G where
  op := HAdd.hAdd

class AddSemigroup (G : Type*) extends Add G where
  protected assoc : ∀ (a b c : G), (a + b) + c = a + (b + c)

instance [AddSemigroup G] : Semigroup G where
  assoc := AddSemigroup.assoc

theorem add_assoc {G : Type*} [AddSemigroup G] (a b c : G) : (a + b) + c = a + (b + c) :=
  assoc a b c

/- ... -/
