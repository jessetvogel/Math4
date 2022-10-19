import Math.Algebra.Basic
import Math.SetTheory.FinSet

open SetTheory

namespace Algebra

variable (α : Type u) (β : Type v) [Zero β]

structure FinSupport where
  map : α → β
  support : FinSet α
  fin_support : ∀ (x : α), x ∈ support ↔ map x ≠ 0

def FinSupport.of_map {A : FinSet α} (f : α → β) (hf : ∀ (x : α), f x ≠ 0 → x ∈ A) : FinSupport α β := {
  map := f,
  support := A.filter (λ x => f x ≠ 0),
  fin_support := λ x => ⟨λ hx => hx.2, λ hx => ⟨hf x hx, hx⟩⟩
}

instance (β : Type v) [hβ : AddZero β] : Add (FinSupport α β) where
  add f g := {
    map := λ x => f.map x + g.map x,
    support := (f.support ∪ g.support).filter (λ x => f.map x + g.map x ≠ 0),
    fin_support := λ x => by {
      constructor;
      exact λ hx => hx.2;
      intro hx;
      constructor;
      {
      have q : f.map x ≠ 0 ∨ g.map x ≠ 0 := by {
        dsimp at hx;
        by_cases hf : f.map x = 0;
        apply Or.inr;
        rw [hf] at hx;
        rw [hβ.zero_add] at hx;
        exact hx;
        exact Or.inl hf;
      }
      cases q with
        | inl q => {
          apply Or.inl;
          show x ∈ f.support;
          rw [f.fin_support x];
          exact q;
        }
        | inr q => {
          apply Or.inr;
          show x ∈ g.support;
          rw [g.fin_support x];
          exact q;
        }
      }
      exact hx;
    }
  }

instance [MulZero β] : Mul (FinSupport α β) where
  mul f g := {
    map := λ x => f.map x * g.map x,
    support := {
      set := λ x => f.map x * g.map x ≠ 0,
      finite := sorry,
    },
    fin_support := λ _ => ⟨id, id⟩,
  }

instance [Neg β] : Neg (FinSupport α β) where
  neg f := {
    map := λ x => -f.map x,
    support := {
      set := λ x => -f.map x ≠ 0,
      finite := sorry, -- TODO: this needs more assumptions
    },
    fin_support := λ _ => ⟨id, id⟩,
  }

end Algebra
