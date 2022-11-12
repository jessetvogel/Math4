namespace Algebra

class One (α : Type u) where
  one : α
class Inv (α : Type u) where
  inv : α → α
class Zero (α : Type u) where
  zero : α
class SMul (α : Type u) (β : Type v) where
  smul : α → β → β
class Bracket (α : Type u) where
  bracket : α → α → α

instance One.toOfNat1 [inst : One α] : OfNat α 1 where
  ofNat := inst.one
instance Zero.toOfNat0 [inst : Zero α] : OfNat α 0 where
  ofNat := inst.zero

class AddZero (α : Type u) extends Add α, Zero α where
  add_zero : ∀ (x : α), x + 0 = x
  zero_add : ∀ (x : α), 0 + x = x

class MulOne (α : Type u) extends Mul α, One α where
  mul_one : ∀ (x : α), x * 1 = x
  one_mul : ∀ (x : α), 1 * x = x

class MulZero (α : Type u) extends Mul α, Zero α where
  mul_zero : ∀ (x : α), x * 0 = 0
  zero_mul : ∀ (x : α), 0 * x = 0

postfix:max "⁻¹" => Inv.inv
infixr:70 " • " => SMul.smul
notation:max "⁅" x ", " y "⁆" => Bracket.bracket x y

-- Morphisms
class MulHom (f : α → β) [Mul α] [Mul β] : Prop where
  map_mul : ∀ (x y : α), f (x * y) = (f x) * (f y)
class AddHom (f : α → β) [Add α] [Add β] : Prop where
  map_add : ∀ (x y : α), f (x + y) = (f x) + (f y)
class ZeroHom (f : α → β) [Zero α] [Zero β] : Prop where
  map_zero : f 0 = 0
class OneHom (f : α → β) [One α] [One β] : Prop where
  map_one : f 1 = 1
class InvHom (f : α → β) [Inv α] [Inv β] : Prop where
  map_inv : ∀ (x : α), f (x⁻¹) = (f x)⁻¹
class SMulHom (α : Type u) (f : β → γ) [SMul α β] [SMul α γ] : Prop where
  map_smul : ∀ (x : α) (m : β), f (x • m) = x • f m
class BracketHom (f : α → β) [Bracket α] [Bracket β] : Prop where
  map_bracket : ∀ (x y : α), f ⁅x, y⁆ = ⁅f x, f y⁆

-- The identity map has lots of these
instance [Mul α] : MulHom (id : α → α) where
  map_mul := λ _ _ => by rfl
instance [Add α] : AddHom (id : α → α) where
  map_add := λ _ _ => by rfl
instance [Zero α] : ZeroHom (id : α → α) where
  map_zero := by rfl
instance [One α] : OneHom (id : α → α) where
  map_one := by rfl
instance [Inv α] : InvHom (id : α → α) where
  map_inv := λ _ => by rfl
instance [SMul α β] : SMulHom α (id : β → β) where
  map_smul := λ _ _ => by rfl

-- Preserved under composition
instance MulHom.comp (g : β → γ) (f : α → β) [Mul α] [Mul β] [Mul γ] [hf : MulHom f] [hg : MulHom g] : MulHom (g ∘ f) where
  map_mul := λ _ _ => by unfold Function.comp; rw [hf.map_mul, hg.map_mul]
instance AddHom.comp (g : β → γ) (f : α → β) [Add α] [Add β] [Add γ] [hf : AddHom f] [hg : AddHom g] : AddHom (g ∘ f) where
  map_add := λ _ _ => by unfold Function.comp; rw [hf.map_add, hg.map_add]
instance ZeroHom.comp (g : β → γ) (f : α → β) [Zero α] [Zero β] [Zero γ] [hf : ZeroHom f] [hg : ZeroHom g] : ZeroHom (g ∘ f) where
  map_zero := by unfold Function.comp; rw [hf.map_zero, hg.map_zero];
instance OneHom.comp (g : β → γ) (f : α → β) [One α] [One β] [One γ] [hf : OneHom f] [hg : OneHom g] : OneHom (g ∘ f) where
  map_one := by unfold Function.comp; rw [hf.map_one, hg.map_one];
instance InvHom.comp (g : β → γ) (f : α → β) [Inv α] [Inv β] [Inv γ] [hf : InvHom f] [hg : InvHom g] : InvHom (g ∘ f) where
  map_inv := λ _ => by unfold Function.comp; rw [hf.map_inv, hg.map_inv];
instance SMulHom.comp (g : γ → δ) (f : β → γ) [SMul α β] [SMul α γ] [SMul α δ] [hf : SMulHom α f] [hg : SMulHom α g] : SMulHom α (g ∘ f) where
  map_smul := λ _ _ => by unfold Function.comp; rw[hf.map_smul, hg.map_smul];

end Algebra
