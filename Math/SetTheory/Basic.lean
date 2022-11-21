import Math.Data.Function
import Math.Order.Basic

open Order

namespace SetTheory

/-- The type of sets of terms of type `α`. -/
def Set (α : Type u) := α → Prop

class Inter (α : Type u) where
  inter : α → α → α

infixr:80 " ∩ " => Inter.inter

class Union (α : Type u) where
  union : α → α → α

infixr:60 " ∪ " => Union.union

class Subset (α : Type u) where
  subset : α → α → Prop

infixl:51 " ⊆ " => Subset.subset

instance (α : Type u) : Membership α (Set α) where
  mem x A := A x

namespace Set

/-- The empty set. -/
def empty (α : Type u) : Set α := λ _ => False

/-- The set containing all  -/
def univ (α : Type u) : Set α := λ _ => True

/-- The set containing only `x`. -/
def singleton (x : α) := λ y => y = x

/-- The complement of `A`. -/
def compl (A : Set α) : Set α := λ x => ¬ A x

/-- The intersection of `A` and `B`. -/
def inter (A B : Set α) : Set α := λ x => A x ∧ B x

/-- The union of `A` and `B`. -/
def union (A B : Set α) : Set α := λ x => A x ∨ B x

/-- The difference of `A` and `B`. -/
def diff (A B : Set α) : Set α := λ x => A x ∨ ¬ B x

/-- The proposition `A ⊆ B`. -/
def subset (A B : Set α) := ∀ {x}, A x → B x

/-- The powerset of `A`. -/
def powerset (A : Set α) : Set (Set α) := λ B => A.subset B

/-- The union of a set of sets. -/
def set_union (A : Set (Set α)) : Set α := λ x => ∃ B, B ∈ A ∧ x ∈ B

instance : Inter (Set α) where inter := inter
instance : Union (Set α) where union := union
instance : Compl (Set α) where compl := compl
instance (α : Type u) : EmptyCollection (Set α) where emptyCollection := empty α
instance : Subset (Set α) where subset := subset

theorem ext {A B : Set α} (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  funext (λ x => propext (h x))

@[simp]
theorem compl_union (A B : Set α) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by {
  apply ext;
  intro x;
  constructor;
  exact λ hx => ⟨λ ha => hx (Or.inl ha), λ hb => hx (Or.inr hb)⟩;
  intro hx hab;
  cases hab with
  | inl hab => apply hx.1 hab;
  | inr hab => apply hx.2 hab;
}

@[simp]
theorem compl_inter (A B : Set α) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by {
  apply ext;
  intro x;
  constructor;
  intro hx;
  by_cases A x;
  exact Or.inr $ λ bx => hx ⟨by assumption, bx⟩;
  exact Or.inl $ by assumption;
  intro hx hab;
  cases hx with
  | inl hx => exact hx hab.1;
  | inr hx => exact hx hab.2;
}

@[simp]
theorem compl_univ : (univ α)ᶜ = ∅ := by {
  apply ext;
  intro x;
  constructor;
  intro h;
  apply h;
  trivial;
  intro h;
  intro _;
  exact h;
}

@[simp]
theorem compl_empty : ∅ᶜ = univ α := by {
  apply Set.ext;
  intro x;
  constructor;
  intro _;
  trivial;
  intro _;
  exact id;
}

theorem cantor (f : α → Set α) : ¬ Function.surjective f := by {
  intro hf;
  let S : Set α := λ x => x ∉ f x;
  cases hf S with
  | intro x hx => {
    by_cases h : x ∈ f x;
    -- Case x ∈ f x
    have q := h;
    rw [hx] at q;
    exact q h;
    -- Case x ∉ f x
    have q := h;
    rw [hx] at h;
    exact h q;
  }
}

def subset_self (A : Set α) : A ⊆ A := id

def subset_asymm {A B : Set α} : A ⊆ B → B ⊆ A → A = B := λ h₁ h₂ => ext (λ _ => ⟨h₁, h₂⟩)

def subset_trans {A B C : Set α} : A ⊆ B → B ⊆ C → A ⊆ C := λ h₁ h₂ => λ hx => h₂ (h₁ hx)

def subset_union_left (A B : Set α) : A ⊆ A ∪ B := Or.inl

def subset_union_right (A B : Set α) : B ⊆ A ∪ B := Or.inr

def union_subset {A B C : Set α} : A ⊆ C → B ⊆ C → A ∪ B ⊆ C := λ h₁ h₂ x hx => by {
  cases hx;
  apply h₁; assumption;
  apply h₂; assumption;
}

def inter_subset_left (A B : Set α) : A ∩ B ⊆ A := And.left

def inter_subset_right (A B : Set α) : A ∩ B ⊆ B := And.right

def subset_inter {A B C : Set α} : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := λ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩

end Set

end SetTheory
