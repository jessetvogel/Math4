import Math.CategoryTheory.Site.Sieve

open SetTheory

namespace CategoryTheory

structure GrothendieckTopology (C : Category) where
  cov : (X : C.obj) → Set (Sieve X)
  max : ∀ X, Sieve.max X ∈ cov X
  pullback : ∀ {X Y S} (_ : S ∈ cov X) (f : C.hom Y X), S.pullback f ∈ cov Y
  other : ∀ {X R S} (_ : S ∈ cov X) (_ : ∀ {Y} {f : C.hom Y X} (_ : f ∈ S.maps), R.pullback f ∈ cov Y), R ∈ cov X

namespace GrothendieckTopology

theorem subsieve (J : GrothendieckTopology C) (hR : R ∈ J.cov X) {S : Sieve X} (hRS : R.subsieve S) : S ∈ J.cov X := by {
  apply J.other hR;
  intro _ f hf;
  have q : S.pullback f = Sieve.max _ := by {
    unfold Sieve.pullback, Sieve.max;
    congr;
    funext _;
    apply Set.ext;
    intro g;
    constructor;
    exact λ _ => trivial;
    exact λ _ => S.comp (hRS hf) g;
  };
  rw [q];
  exact J.max _;
}

theorem intersection (J : GrothendieckTopology C) (hR : R ∈ J.cov X) (hS : S ∈ J.cov X) : R.intersection S ∈ J.cov X := by {
  apply J.other hR;
  intro _ f hf;
  have q : (R.intersection S).pullback f = S.pullback f := by {
    unfold Sieve.pullback, Sieve.intersection;
    congr;
    funext Y;
    apply Set.ext;
    exact λ g => ⟨λ hg => hg.2, λ hg => ⟨R.comp hf _, hg⟩⟩;
  };
  rw [q];
  exact J.pullback hS _;
}

def smallest (C : Category) : GrothendieckTopology C := {
  cov := λ X S => S = Sieve.max X,
  max := λ X => by trivial,
  pullback := λ hS f => by simp [hS, Sieve.pullback, Sieve.max]; rfl,
  other := λ {X R S} hS h => by {
    have q : (C.id X) ∈ S.maps := by simp [hS, Sieve.max, Set.univ];
    specialize h q;
    simp at h;
    exact h;
  }
}

def biggest (C : Category) : GrothendieckTopology C := {
  cov := λ X _ => True,
  max := λ _ => by simp,
  pullback := by simp,
  other := by simp,
}

end GrothendieckTopology

end CategoryTheory
