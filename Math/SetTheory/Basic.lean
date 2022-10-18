import Math.Data.Function

namespace SetTheory

/-- The type of sets of terms of type `α`. -/
def Set (α : Type u) := α → Prop

class Inter (α : Type u) where
  inter : α → α → α

class Union (α : Type u) where
  union : α → α → α

class Compl (α : Type u) where
  compl : α → α

class Subset (α : Type u) where
  subset : α → α → Prop

infixr:60 " ∪ " => Union.union
infixr:80 " ∩ " => Inter.inter
infixl:51 " ⊆ " => Subset.subset
postfix:max " ᶜ " => Compl.compl

instance (α : Type u) : Membership α (Set α) where mem x A := A x

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
def subset (A B : Set α) := ∀ x, A x → B x

/-- The powerset of `A`. -/
def powerset (A : Set α) : Set (Set α) := λ B => A.subset B

/-- The union of a set of sets. -/
def set_union (A : Set (Set α)) : Set α := λ x => ∃ B, B ∈ A ∧ x ∈ B

instance : Inter (Set α) where inter := inter
instance : Union (Set α) where union := union
instance : Compl (Set α) where compl := compl
instance (α : Type u) : EmptyCollection (Set α) where emptyCollection := empty α
instance : Subset (Set α) where subset := subset

theorem ext (A B : Set α) (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  funext (λ x => propext (h x))

@[simp]
theorem compl_union (A B : Set α) : (A ∪ B)ᶜ  = Aᶜ ∩ Bᶜ := by {
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

end Set

end SetTheory
