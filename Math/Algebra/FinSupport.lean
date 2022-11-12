import Math.Algebra.Basic
import Math.SetTheory.FinSet.Basic

open SetTheory

namespace Algebra

structure FinSupport (α : Type u) (β : Type v) [Zero β] where
  map : α → β
  support : FinSet α
  fin_support : ∀ (x : α), x ∈ support ↔ map x ≠ 0

variable {α : Type u} {β : Type v} [Zero β]

def FinSupport.of_map {A : FinSet α} (f : α → β) (hf : ∀ (x : α), f x ≠ 0 → x ∈ A) : FinSupport α β := {
  map := f,
  support := A.filter (λ x => f x ≠ 0),
  fin_support := λ x => ⟨λ hx => hx.2, λ hx => ⟨hf x hx, hx⟩⟩
}

def FinSupport.zero : FinSupport α β := {
  map := λ _ => 0,
  support := ∅,
  fin_support := λ x => by {
    constructor;
    intro _; contradiction;
    intro _; contradiction;
  }
}

instance : Zero (FinSupport α β) where
  zero := FinSupport.zero

def FinSupport.of_single (a : α) (b : β) : FinSupport α β := if b = 0 then ∅ else {
  map := λ x => if x = a then b else 0,
  support := FinSet.of_single a,
  fin_support := sorry
}

def FinSupport.add {β : Type v} [hβ : AddZero β] (f g : FinSupport α β) : FinSupport α β := {
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

instance (β : Type v) [AddZero β] : Add (FinSupport α β) where
  add := FinSupport.add

def FinSupport.mul [MulZero β] (f g : FinSupport α β): FinSupport α β := {
  map := λ x => f.map x * g.map x,
  support := {
    set := λ x => f.map x * g.map x ≠ 0,
    finite := sorry,
  },
  fin_support := sorry --λ _ => ⟨id, id⟩,
}

instance [MulZero β] : Mul (FinSupport α β) where
  mul := FinSupport.mul

def FinSupport.neg [Neg β] (f : FinSupport α β) : FinSupport α β := {
  map := λ x => - f.map x,
  support := { -- Should be the same support, but need the assumption that x ≠ 0 → -x ≠ 0
    set := λ x => -f.map x ≠ 0,
    finite := sorry,
  },
  fin_support := λ _ => ⟨id, id⟩,
}

instance [Neg β] : Neg (FinSupport α β) where
  neg := FinSupport.neg

end Algebra
