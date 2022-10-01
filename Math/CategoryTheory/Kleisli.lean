import Math.CategoryTheory.Monad

namespace CategoryTheory

def Kleisli (M : Monad C) : Category := {
  obj := C.obj,
  hom := λ X Y => C.hom X (M.T.obj Y),
  id := λ X => M.η.map X,
  comp := λ g f => C.comp (M.μ.map _) (C.comp (M.T.map g) f),
  comp_id := λ {X Y} f => by {
    dsimp;
    rw [← M.η.natural f];
    unfold Functor.id;
    simp;
    rw [← C.assoc, M.mul_one, C.id_comp];
  },
  id_comp := λ f => by {
    dsimp;
    rw [← C.assoc, M.one_mul];
    simp;
  },
  assoc := λ {W X Y Z} h g f => by {
    simp;
    rw [← C.assoc, M.assoc];
    simp;
    congr;
    suffices s : C.comp (M.μ.map (M.T.obj Z)) (M.T.map (M.T.map h)) = C.comp (M.T.map h) (M.μ.map Y) by rw [← C.assoc, s, C.assoc];
    let q := M.μ.natural h;
    unfold Functor.comp at q;
    simp at q;
    exact q;
  },
}

def Kleisli.free (M : Monad C) : Functor C (Kleisli M) := {
  obj := λ X => X,
  map := λ f => C.comp (M.η.map _) f,
  map_id := λ X => by unfold Kleisli; simp,
  map_comp := λ {X Y Z} g f => by {
    unfold Kleisli;
    simp;
    rw [← C.assoc (M.μ.map Z), M.one_mul];
    have q := M.η.natural f; unfold Functor.id at q; simp at q;
    rw [q, ← C.assoc (M.T.map g), ← M.T.map_comp];
    have q' := M.η.natural (C.comp g f); unfold Functor.id at q'; dsimp at q';
    rw [← q'];
    rw [C.id_comp (C.comp (M.η.map Z) _)];
  },
}

def Kleisli.forget (M : Monad C) : Functor (Kleisli M) C := {
  obj := λ X => M.T.obj X,
  map := λ f => C.comp (M.μ.map _) (M.T.map f),
  map_id := λ X => by unfold Kleisli; simp,
  map_comp := λ {X Y Z} g f => by {
    unfold Kleisli;
    simp;
    -- μ_Z ∘ T μ_Z ∘ T T g) ∘ T f = μ_Z ∘ T g ∘ μ_Y ∘ T f
    sorry;
  },
}

def Kleisli.adjunction (M : Monad C) : Kleisli.free M ⊣ Kleisli.forget M := {
  equiv := λ X Y => {
    to := λ f => f,
    inv := λ f => f,
    left_inv := by simp,
    right_inv := by simp,
  },
  natural := λ {X X' Y Y'} f g h => by {
    unfold Kleisli, Kleisli.free, Kleisli.forget;
    simp;
    congr;
    -- Get rid of f
    rw [← C.assoc _ _ f, ← C.assoc]; congr;
    -- Use Kleisli.comp_id h
    have q := (Kleisli M).comp_id h;
    unfold Kleisli, Kleisli.free at q;
    simp at q;
    rw [q];
  },
}


end CategoryTheory
