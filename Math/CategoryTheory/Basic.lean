import Math.Data.Function

namespace CategoryTheory

class Category (α : Sort u) where
  hom     : α → α → Sort v
  id      : ∀ (X : α), hom X X
  comp    : ∀ {X Y Z : α}, (hom Y Z) → (hom X Y) → (hom X Z)
  comp_id : ∀ {X Y : α} (f : hom X Y), comp f (id X) = f := by simp
  id_comp : ∀ {X Y : α} (f : hom X Y), comp (id Y) f = f := by simp
  comp_assoc   : ∀ {W X Y Z : α} (h : hom Y Z) (g : hom X Y) (f : hom W X), comp (comp h g) f = comp h (comp g f) := by simp

infixr:80 " ∘ " => Category.comp
prefix:max "𝟙 " => Category.id

attribute [simp] Category.comp_id Category.id_comp Category.comp_assoc

variable [Category α] {X Y : α}

open Category

/-- A morphism f : X → Y is mono if f ∘ g = f ∘ h implies g = h for all g and h. -/
class mono (f : hom X Y) : Prop :=
  cancel : ∀ {Z : α} {g h : hom Z X}, f ∘ g = f ∘ h → g = h

/-- A morphism f : X → Y is epi if g ∘ f = h ∘ f implies g = h for all g and h. -/
class epi (f : hom X Y) : Prop :=
  cancel : ∀ {Z : α} {g h : hom Y Z}, g ∘ f = h ∘ f → g = h

class split_mono (f : hom X Y) : Prop :=
  left_inv : ∃ g, g ∘ f = 𝟙 X

class split_epi (f : hom X Y) : Prop :=
  right_inv : ∃ g, f ∘ g = 𝟙 Y

/-- If `f` and `g` are mono, then so is `g ∘ f`. -/
instance mono_comp (g : hom Y Z) (f : hom X Y) [hf : mono f] [hg : mono g] : mono (g ∘ f) where
  cancel h := by simp at h; exact hf.cancel (hg.cancel h)

/-- If `f` and `g` are epi, then so is `g ∘ f`. -/
instance epi_comp (g : hom Y Z) (f : hom X Y) [hf : epi f] [hg : epi g] : epi (g ∘ f) where
  cancel h := by rw [← comp_assoc, ← comp_assoc] at h; exact hg.cancel (hf.cancel h)

/-- If `g ∘ f` is mono, then so is `f`. -/
theorem mono_right (g : hom Y Z) (f : hom X Y) [h : mono (g ∘ f)] : mono f :=
  ⟨λ h' => by apply h.cancel; simp; rw [h']⟩

/-- If `g ∘ f` is epi, then so is `g`. -/
theorem epi_left (g : hom Y Z) (f : hom X Y) [h : epi (g ∘ f)] : epi g :=
  ⟨λ h' => by apply h.cancel; rw [← comp_assoc, h', comp_assoc]⟩

/-- If `f` is split mono, then it is mono. -/
instance mono_of_split_mono (f : hom X Y) [h : split_mono f] : mono f where
  cancel t := by {
    match h.left_inv with
    | Exists.intro g hg => {
      have t := congrArg (comp g) t;
      rw [← Category.comp_assoc, ← Category.comp_assoc, hg, Category.id_comp, Category.id_comp] at t;
      exact t;
    }
  }

/-- If `f` is split epi, then it is epi. -/
instance epi_of_split_epi (f : hom X Y) [h : split_epi f] : epi f where
  cancel {Z' g' h'} t := by {
    match h.right_inv with
    | Exists.intro g hg => {
      have t := congrArg (λ k => comp k g) t;
      simp [hg] at t;
      exact t;
    }
  }

structure Iso (X Y : α) where
  hom : Category.hom X Y
  inv : Category.hom Y X
  inv_comp : inv ∘ hom = 𝟙 X := by simp
  comp_inv : hom ∘ inv = 𝟙 Y := by simp

def Iso.id (X : α) : Iso X X := {
  hom := 𝟙 X,
  inv := 𝟙 X
}

def Iso.comp {X Y Z : α} (g : Iso Y Z) (f : Iso X Y) : Iso X Z := {
  hom := g.hom ∘ f.hom,
  inv := f.inv ∘ g.inv,
  inv_comp := by rw [comp_assoc, ← comp_assoc g.inv, g.inv_comp, id_comp, f.inv_comp],
  comp_inv := by rw [comp_assoc, ← comp_assoc f.hom, f.comp_inv, id_comp, g.comp_inv],
}

def Iso.inverse (f : Iso X Y) : Iso Y X := {
  hom := f.inv,
  inv := f.hom,
  inv_comp := f.comp_inv,
  comp_inv := f.inv_comp
}

class initial (X : α) : Prop where
  is_initial : ∀ (Y : α), ∃ (f : hom X Y), ∀ (g : hom X Y), f = g

class terminal (Y : α) : Prop where
  is_terminal : ∀ (X : α), ∃ (f : hom X Y), ∀ (g : hom X Y), f = g

class zero (X : α) : Prop where
  is_zero : initial X ∧ terminal X

-- structure Isomorphism {C : Category} (X Y : C.obj) where
--   f : C.hom X Y
--   g : C.hom Y X
--   comp_gf : g ∘ f = C.id X := by simp
--   comp_fg : f ∘ g = C.id Y := by simp

-- infix:80 " ≅ " => Isomorphism

-- def Isomorphism.comp (i₂ : Y ≅ Z) (i₁ : X ≅ Y) : X ≅ Z := {
--   f := i₂.f ∘ i₁.f,
--   g := i₁.g ∘ i₂.g,
--   comp_gf := by rw [C.comp_assoc, ← C.comp_assoc i₂.g, i₂.comp_gf, C.id_comp, i₁.comp_gf],
--   comp_fg := by rw [C.comp_assoc, ← C.comp_assoc i₁.f, i₁.comp_fg, C.id_comp, i₂.comp_fg],
-- }

-- def Isomorphism.id (X : C.obj) : X ≅ X := {
--   f := C.id X,
--   g := C.id X
-- }

namespace Category

class thin (α : Type u) [Category α] : Prop :=
  is_thin : ∀ {X Y : α} (f g : hom X Y), f = g

-- Opposite category
-- def op : Category := {
--   obj := C.obj,
--   hom := λ X Y => C.hom Y X,
--   id := C.id,
--   comp := λ g f => f ∘ g,
-- }

/-- The product category. -/
instance product [Category α] [Category β] : Category (α × β) where
  hom X Y := hom X.1 Y.1 × hom X.2 Y.2
  id X := ⟨id X.1, id X.2⟩
  comp g f := ⟨g.1 ∘ f.1, g.2 ∘ f.2⟩
  comp_id f := by simp
  id_comp f := by simp
  comp_assoc h g f := by simp

/-- The sum category. -/
instance sum [Category α] [Category β] : Category (Sum α β) where
  hom X Y := match X, Y with
    | Sum.inl X, Sum.inl Y => hom X Y
    | Sum.inl _, Sum.inr _ => PEmpty
    | Sum.inr _, Sum.inl _ => PEmpty
    | Sum.inr X, Sum.inr Y => hom X Y
  id X := match X with
    | Sum.inl X => id X
    | Sum.inr X => id X
  comp {X Y Z} g f := match X, Y, Z, g, f with
    | Sum.inl _, Sum.inl _, Sum.inl _, g, f => g ∘ f
    | Sum.inr _, Sum.inr _, Sum.inr _, g, f => g ∘ f
  comp_id {X Y} f := match X, Y, f with
    | Sum.inl _, Sum.inl _, f => comp_id f
    | Sum.inr _, Sum.inr _, f => comp_id f
  id_comp {X Y} f := match X, Y, f with
    | Sum.inl _, Sum.inl _, f => id_comp f
    | Sum.inr _, Sum.inr _, f => id_comp f
  comp_assoc {W X Y Z} h g f := match W, X, Y, Z, h, g, f with
    | Sum.inl _, Sum.inl _, Sum.inl _, Sum.inl _, h, g, f => comp_assoc h g f
    | Sum.inr _, Sum.inr _, Sum.inr _, Sum.inr _, h, g, f => comp_assoc h g f

end Category

/-- Category of types. -/
instance CatType : Category (Sort u) where
  hom α β := α → β
  id _ := id
  comp := Function.comp
  comp_id _ := by rfl
  id_comp _ := by rfl
  comp_assoc _ _ _ := by rfl

-- A morphism in CatType is epi if and only if it is surjective
def CatType.epi_iff_surj (f : CatType.hom α β) : epi f ↔ Function.surjective f := ⟨
  λ hf y => by {
    apply Classical.byContradiction;
    intro h;
    sorry;
  },
  λ h => ⟨ λ t => by funext y; cases h y with | intro x hx => rw [← hx]; exact congrFun t x⟩
⟩

-- A morphism in CatType is mono if and only if it is injective
def CatType.mono_iff_inj (f : CatType.hom α β) : mono f ↔ Function.injective f := ⟨
  λ hf x y hxy => by {
    -- Construct two functions, g h : 1 → X, which sends to x and y
    let g : PUnit → α := λ _ => x;
    let h : PUnit → α := λ _ => y;
    -- Then f ∘ g = f ∘ h by assumption
    have t : CatType.comp f g = CatType.comp f h := by funext _; exact hxy;
    -- Cancel f using mono
    exact congrFun (hf.cancel t) PUnit.unit;
  },
  λ hf => ⟨λ t => by funext _; exact hf (congrFun t _)⟩
⟩

end CategoryTheory
