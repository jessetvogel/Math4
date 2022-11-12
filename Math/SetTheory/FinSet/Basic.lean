import Math.SetTheory.Basic

namespace SetTheory

class Set.finite {α : Type u} (A : Set α) : Prop where
  is_finite : ∃ (n : Nat) (f : Fin n → α), ∀ (y : α), y ∈ A → ∃ (x : Fin n), f x = y

structure FinSet (α : Type u) where
  set : Set α
  finite : set.finite

def FinSet.of_set {α : Type u} (A : Set α) [hA : A.finite] : FinSet α := {
  set := A,
  finite := hA
}

def FinSet.of_single {α : Type u} (x : α) : FinSet α := {
  set := λ y => x = y,
  finite := ⟨Exists.intro 1 $ Exists.intro (λ _ => x) $ λ _ h => Exists.intro 0 h⟩
}

def FinSet.filter {α : Type u} (A : FinSet α) (h : α → Prop) : FinSet α where
  set x := x ∈ A.set ∧ h x
  finite := ⟨
    match A.finite.is_finite with
    | Exists.intro n (Exists.intro f hf) =>
      Exists.intro n $ Exists.intro f $ λ y hy => hf y hy.1
  ⟩

instance (α : Type u) : Membership α (FinSet α) where
  mem x A := x ∈ A.set

namespace FinSet

def inter (A B : FinSet α) : FinSet α := {
  set := A.set ∩ B.set,
  finite := ⟨by {
    cases A.finite.is_finite with
    | intro n hn => {
      cases hn with
      | intro f hf => {
        apply Exists.intro n;
        apply Exists.intro f;
        intro y hy;
        cases hf y hy.1 with
        | intro x hx =>
          exact Exists.intro x hx;
      }
    }
  }⟩
}

def union (A B : FinSet α) : FinSet α := {
  set := A.set ∪ B.set,
  finite := ⟨by {
    -- Unfold finiteness of A and B
    match A.finite.is_finite, B.finite.is_finite with
    | Exists.intro m (Exists.intro f hf), Exists.intro n (Exists.intro g hg) => {
      -- Define a surjection Fin (m + n) → A ∪ B
      let h : Fin (m + n) → α := λ k =>
        if k < m
          then f { val := k, isLt := sorry }
          else g { val := k - m, isLt := sorry };
      -- Use this surjection
      apply Exists.intro (m + n);
      apply Exists.intro h;
      intro y hy;
      cases hy with
      | inl hy => { -- Case y ∈ A
        cases hf y hy with
        | intro x hx => {
          apply Exists.intro { val := x.val, isLt := sorry };
          simp [← hx, x.isLt];
        }
      }
      | inr hy => { -- Case y ∈ B
        cases hg y hy with
        | intro x hx => {
          apply Exists.intro { val := m + x.val, isLt := sorry };
          have q₁ : ¬ (m + x.val < m) := sorry;
          have q₂ : m + x.val - m = x.val := sorry;
          simp [← hx, q₁, q₂];
        }
      }
    }
  }⟩
}

instance (α : Type u) : Union (FinSet α) where
  union := union

instance (α : Type u) : Inter (FinSet α) where
  inter := inter

instance (α : Type u) : EmptyCollection (FinSet α) := {
  emptyCollection := {
    set := ∅,
    finite := by {
      constructor;
      apply Exists.intro 0;
      apply Exists.intro (λ x => by {
        have := x.isLt;
        contradiction;
      });
      intro y hy;
      contradiction;
    }
  }
}

instance (α : Type u) : Subset (FinSet α) where
  subset A B := A.set ⊆ B.set

end FinSet

end SetTheory
