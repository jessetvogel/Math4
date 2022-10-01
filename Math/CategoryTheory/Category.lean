import Math.Data.Function

namespace CategoryTheory

universe u v

structure Category where
  obj     : Sort u
  hom     : obj → obj → Sort v
  id      : ∀ (X : obj), hom X X
  comp    : ∀ {X Y Z : obj}, (hom Y Z) → (hom X Y) → (hom X Z)
  comp_id : ∀ {X Y : obj} (f : hom X Y), comp f (id X) = f := by simp
  id_comp : ∀ {X Y : obj} (f : hom X Y), comp (id Y) f = f := by simp
  assoc   : ∀ {W X Y Z : obj} (h : hom Y Z) (g : hom X Y) (f : hom W X), comp (comp h g) f = comp h (comp g f) := by simp

infixr:80 " ∘ " => Category.comp _

attribute [simp] Category.comp_id Category.id_comp Category.assoc

variable {C : Category} {X Y : C.obj}

class mono (f : C.hom X Y) : Prop :=
  cancel : ∀ {Z : C.obj} {g h : C.hom Z X}, f ∘ g = f ∘ h → g = h

class epi (f : C.hom X Y) : Prop :=
  cancel : ∀ {Z : C.obj} {g h : C.hom Y Z}, g ∘ f = h ∘ f → g = h

class split_mono (f : C.hom X Y) : Prop :=
  left_inv : ∃ g, g ∘ f = C.id X

class split_epi (f : C.hom X Y) : Prop :=
  right_inv : ∃ g, f ∘ g = C.id Y

-- The composition of monos is mono
theorem mono_comp (hg : mono g) (hf : mono f) : mono (g ∘ f) :=
  ⟨ λ h => by simp at h; exact hf.cancel (hg.cancel h) ⟩

-- The composition of epis is epi
theorem epi_comp (hg : epi g) (hf : epi f) : epi (g ∘ f) :=
  ⟨ λ h => by rw [← Category.assoc, ← Category.assoc] at h; exact hg.cancel (hf.cancel h) ⟩

-- If `g ∘ f` is mono, then `f` is mono
theorem mono_right (h : mono (g ∘ f)) : mono f :=
  ⟨ λ h' => by apply h.cancel; simp; rw [h'] ⟩

-- If `g ∘ f` is epi, then `g` is epi
theorem epi_left (h : epi (g ∘ f)) : epi g :=
  ⟨ λ h' => by apply h.cancel; rw [← Category.assoc, h', Category.assoc] ⟩

-- Every split mono is a mono
theorem mono_of_split_mono (h : split_mono f) : mono f := ⟨
  λ t => by {
    match h.left_inv with
    | Exists.intro g hg => {
      have t := congrArg (Category.comp _ g) t;
      rw [← Category.assoc, ← Category.assoc, hg, Category.id_comp, Category.id_comp] at t;
      exact t;
    }
  }
⟩

-- Every split epi is an epi
theorem epi_of_split_epi (h : split_epi f) : epi f := ⟨
  λ {Z' g' h'} t => by {
    match h.right_inv with
    | Exists.intro g hg => {
      have t := congrArg (λ k => Category.comp _ k g) t;
      simp [hg] at t;
      exact t;
    }
  } 
⟩

namespace Category

class thin (C : Category) : Prop :=
  is_thin : ∀ X Y (f g : C.hom X Y), f = g

class iso (f : C.hom X Y) : Prop :=
  is_iso : ∃ (g : C.hom Y X), g ∘ f = C.id X ∧ f ∘ g = C.id Y

class initial (X : C.obj) : Prop :=
  is_initial : ∀ (Y : C.obj), ∃ (f : C.hom X Y), ∀ (g : C.hom X Y), f = g

class terminal (Y : C.obj) : Prop :=
  is_terminal : ∀ (X : C.obj), ∃ (f : C.hom X Y), ∀ (g : C.hom X Y), f = g

class zero (X : C.obj) : Prop :=
  is_zero : C.initial X ∧ C.terminal X

structure Isomorphism {C : Category} (X Y : C.obj) where
  f : C.hom X Y
  g : C.hom Y X
  comp_gf : g ∘ f = C.id X := by simp
  comp_fg : f ∘ g = C.id Y := by simp

infix:80 " ≅ " => Isomorphism

def Isomorphism.comp (i₂ : Y ≅ Z) (i₁ : X ≅ Y) : X ≅ Z := {
  f := i₂.f ∘ i₁.f,
  g := i₁.g ∘ i₂.g,
  comp_gf := by rw [C.assoc, ← C.assoc i₂.g, i₂.comp_gf, C.id_comp, i₁.comp_gf],
  comp_fg := by rw [C.assoc, ← C.assoc i₁.f, i₁.comp_fg, C.id_comp, i₂.comp_fg],
}

def Isomorphism.id (X : C.obj) : X ≅ X := {
  f := C.id X,
  g := C.id X
}

-- Opposite category
def op : Category := {
  obj := C.obj,
  hom := λ X Y => C.hom Y X,
  id := C.id,
  comp := λ g f => f ∘ g,
}

-- Product category
def product (D : Category) : Category := {
  obj := C.obj × D.obj,
  hom := λ X Y => C.hom X.1 Y.1 × D.hom X.2 Y.2,
  id := λ X => ⟨C.id X.1, D.id X.2⟩,
  comp := λ g f => ⟨g.1 ∘ f.1, g.2 ∘ f.2⟩,
}

-- Sum category
def sum (D : Category) : Category := {
  obj := Sum C.obj D.obj,
  hom := λ X Y => match X, Y with
    | Sum.inl X, Sum.inl Y => C.hom X Y
    | Sum.inl _, Sum.inr _ => PEmpty
    | Sum.inr _, Sum.inl _ => PEmpty
    | Sum.inr X, Sum.inr Y => D.hom X Y
  id := λ X => match X with
    | Sum.inl X => C.id X
    | Sum.inr X => D.id X,
  comp := λ {X Y Z} g f => match X, Y, Z, g, f with
    | Sum.inl _, Sum.inl _, Sum.inl _, g, f => g ∘ f
    | Sum.inr _, Sum.inr _, Sum.inr _, g, f => g ∘ f,
  comp_id := λ {X Y} f => match X, Y, f with
    | Sum.inl _, Sum.inl _, f => C.comp_id f
    | Sum.inr _, Sum.inr _, f => D.comp_id f,
  id_comp := λ {X Y} f => match X, Y, f with
    | Sum.inl _, Sum.inl _, f => C.id_comp f
    | Sum.inr _, Sum.inr _, f => D.id_comp f,
  assoc := λ {W X Y Z} h g f => match W, X, Y, Z, h, g, f with
    | Sum.inl _, Sum.inl _, Sum.inl _, Sum.inl _, h, g, f => C.assoc h g f
    | Sum.inr _, Sum.inr _, Sum.inr _, Sum.inr _, h, g, f => D.assoc h g f,
}

end Category

-- Category of types
def CatType : Category := {
  obj := Sort u,
  hom := λ α β => α → β,
  id := λ α X => X,
  comp := λ g f x => g (f x),
}

-- A morphism in CatType is epi if and only if it is surjective
def CatType.epi_iff_surj {X Y : Sort u} (f : CatType.hom X Y) : epi f ↔ Function.surjective f := ⟨
  λ hf y => by sorry,
  λ h => ⟨ λ t => by funext y; match h y with | Exists.intro x hx => rw [← hx]; exact congrFun t x⟩
⟩

-- A morphism in CatType is mono if and only if it is injective
def CatType.mono_iff_inj {X Y : Sort u} (f : CatType.hom X Y) : mono f ↔ Function.injective f := ⟨
  λ hf x y hxy => by {
    -- Construct two functions, g h : 1 → X, which sends to x and y
    let g : PUnit → X := λ _ => x;
    let h : PUnit → X := λ _ => y;
    -- Then f ∘ g = f ∘ h by assumption
    have t : CatType.comp f g = CatType.comp f h := by funext _; exact hxy;
    -- Cancel f using mono
    exact congrFun (hf.cancel t) PUnit.unit;
  },
  λ hf => ⟨λ t => by funext _; exact hf (congrFun t _)⟩
⟩

end CategoryTheory
