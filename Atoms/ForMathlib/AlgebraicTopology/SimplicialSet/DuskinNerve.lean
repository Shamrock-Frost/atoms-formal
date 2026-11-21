import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Functor.StrictlyUnitary
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

namespace CategoryTheory

open Bicategory Simplicial

universe w v u w₁ v₁ u₁ v₂ u₂ v₃ u₃

private theorem eqToHom_conj_heq {B : Type u} [Bicategory.{w, v} B] {a b : B}
    {f f' g g' : a ⟶ b} (p : f = f') (θ : f' ⟶ g') (q : g' = g) :
    eqToHom p ≫ θ ≫ eqToHom q ≍ θ := by
  subst p q
  simp

namespace StrictlyUnitaryLaxFunctor

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w, v₂} C]

theorem ext_of_isLocallyDiscrete [IsLocallyDiscrete C] {F G : StrictlyUnitaryLaxFunctor B C}
    (h_obj : ∀ a, F.obj a = G.obj a) (h_map : ∀ {a b : B} (f : a ⟶ b), F.map f ≍ G.map f) :
    F = G := by
  obtain ⟨⟨⟨⟨⟨Fobj, Fmap⟩, Fmap₂⟩, _, _⟩, FmapId, FmapComp, _, _, _, _, _⟩, _, _⟩ := F
  obtain ⟨⟨⟨⟨⟨Gobj, Gmap⟩, Gmap₂⟩, _, _⟩, GmapId, GmapComp, _, _, _, _, _⟩, _, _⟩ := G
  obtain rfl : Fobj = Gobj := funext h_obj
  obtain rfl : @Fmap = @Gmap := by
    funext a b f
    exact eq_of_heq (h_map f)
  obtain rfl : @Fmap₂ = @Gmap₂ := by
    funext a b f g η
    exact Subsingleton.elim _ _
  obtain rfl : FmapId = GmapId := funext fun _ => Subsingleton.elim _ _
  obtain rfl : @FmapComp = @GmapComp := by
    funext a b c f g
    exact Subsingleton.elim _ _
  rfl

theorem ext_of_isLocallyDiscrete_source [IsLocallyDiscrete B]
    {F G : StrictlyUnitaryLaxFunctor B C}
    (h_obj : ∀ a, F.obj a = G.obj a) (h_map : ∀ {a b : B} (f : a ⟶ b), F.map f ≍ G.map f)
    (h_mapComp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), F.mapComp f g ≍ G.mapComp f g) :
    F = G := by
  obtain ⟨⟨⟨⟨⟨Fobj, Fmap⟩, Fmap₂⟩, Fmap₂_id, _⟩, FmapId, FmapComp, _, _, _, _, _⟩, _,
    FmapId_eq⟩ := F
  obtain ⟨⟨⟨⟨⟨Gobj, Gmap⟩, Gmap₂⟩, Gmap₂_id, _⟩, GmapId, GmapComp, _, _, _, _, _⟩, _,
    GmapId_eq⟩ := G
  obtain rfl : Fobj = Gobj := funext h_obj
  obtain rfl : @Fmap = @Gmap := by
    funext a b f
    exact eq_of_heq (h_map f)
  obtain rfl : @Fmap₂ = @Gmap₂ := by
    funext a b f g η
    obtain rfl := obj_ext_of_isDiscrete η
    obtain rfl : η = 𝟙 f := Subsingleton.elim _ _
    exact (Fmap₂_id f).trans (Gmap₂_id f).symm
  obtain rfl : FmapId = GmapId := funext fun a => (FmapId_eq a).trans (GmapId_eq a).symm
  obtain rfl : @FmapComp = @GmapComp := by
    funext a b c f g
    exact eq_of_heq (h_mapComp f g)
  rfl

theorem mapComp_id_left [IsLocallyDiscrete B] (F : StrictlyUnitaryLaxFunctor B C) {a b : B}
    (f : a ⟶ b) :
    F.mapComp (𝟙 a) f = eqToHom (by rw [F.map_id]) ≫ (λ_ (F.map f)).hom ≫
      eqToHom (congrArg F.map (Strict.id_comp f).symm) := by
  have h := F.map₂_leftUnitor f
  rw [F.mapId_eq_eqToHom, eqToHom_whiskerRight,
    (Subsingleton.elim _ _ : (λ_ f).inv = eqToHom (Strict.id_comp f).symm),
    PrelaxFunctor.map₂_eqToHom] at h
  rw [← cancel_epi ((λ_ (F.map f)).inv ≫ eqToHom (by rw [F.map_id])), Category.assoc, ← h]
  simp

theorem mapComp_id_right [IsLocallyDiscrete B] (F : StrictlyUnitaryLaxFunctor B C) {a b : B}
    (f : a ⟶ b) :
    F.mapComp f (𝟙 b) = eqToHom (by rw [F.map_id]) ≫ (ρ_ (F.map f)).hom ≫
      eqToHom (congrArg F.map (Strict.comp_id f).symm) := by
  have h := F.map₂_rightUnitor f
  rw [F.mapId_eq_eqToHom, whiskerLeft_eqToHom,
    (Subsingleton.elim _ _ : (ρ_ f).inv = eqToHom (Strict.comp_id f).symm),
    PrelaxFunctor.map₂_eqToHom] at h
  rw [← cancel_epi ((ρ_ (F.map f)).inv ≫ eqToHom (by rw [F.map_id])), Category.assoc, ← h]
  simp

private theorem leftUnitor_hom_heq {a b a' b' : C} (ha : a = a') (hb : b = b') {f : a ⟶ b}
    {f' : a' ⟶ b'} (hf : f ≍ f') : (λ_ f).hom ≍ (λ_ f').hom := by
  subst ha hb
  cases hf
  rfl

private theorem rightUnitor_hom_heq {a b a' b' : C} (ha : a = a') (hb : b = b') {f : a ⟶ b}
    {f' : a' ⟶ b'} (hf : f ≍ f') : (ρ_ f).hom ≍ (ρ_ f').hom := by
  subst ha hb
  cases hf
  rfl

theorem ext_of_lt {P : Type u₁} [PartialOrder P]
    {F G : StrictlyUnitaryLaxFunctor (LocallyDiscrete P) C}
    (h_obj : ∀ x, F.obj x = G.obj x)
    (h_map : ∀ {x y : LocallyDiscrete P} (f : x ⟶ y), x.as < y.as → F.map f ≍ G.map f)
    (h_mapComp : ∀ {x y z : LocallyDiscrete P} (f : x ⟶ y) (g : y ⟶ z), x.as < y.as →
      y.as < z.as → F.mapComp f g ≍ G.mapComp f g) :
    F = G := by
  have h_map' {x y : LocallyDiscrete P} (f : x ⟶ y) : F.map f ≍ G.map f := by
    rcases (leOfHom f.as).lt_or_eq with h | h
    · exact h_map f h
    · obtain rfl : x = y := LocallyDiscrete.ext h
      obtain rfl : f = 𝟙 x := Discrete.ext (Subsingleton.elim _ _)
      rw [F.map_id, G.map_id, h_obj x]
  refine ext_of_isLocallyDiscrete_source h_obj h_map' fun {x y z} f g => ?_
  rcases (leOfHom f.as).lt_or_eq with h₁ | h₁
  · rcases (leOfHom g.as).lt_or_eq with h₂ | h₂
    · exact h_mapComp f g h₁ h₂
    · obtain rfl : y = z := LocallyDiscrete.ext h₂
      obtain rfl : g = 𝟙 y := Discrete.ext (Subsingleton.elim _ _)
      rw [F.mapComp_id_right, G.mapComp_id_right]
      exact (eqToHom_conj_heq _ _ _).trans ((rightUnitor_hom_heq (h_obj x) (h_obj y)
        (h_map' f)).trans (eqToHom_conj_heq _ _ _).symm)
  · obtain rfl : x = y := LocallyDiscrete.ext h₁
    obtain rfl : f = 𝟙 x := Discrete.ext (Subsingleton.elim _ _)
    rw [F.mapComp_id_left, G.mapComp_id_left]
    exact (eqToHom_conj_heq _ _ _).trans ((leftUnitor_hom_heq (h_obj x) (h_obj z)
      (h_map' g)).trans (eqToHom_conj_heq _ _ _).symm)

end StrictlyUnitaryLaxFunctor

section LocallyDiscrete

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

@[simps!]
def Functor.toStrictlyUnitaryLaxFunctor (F : C ⥤ D) :
    StrictlyUnitaryLaxFunctor (LocallyDiscrete C) (LocallyDiscrete D) :=
  .mk' {
    obj X := ⟨F.obj X.as⟩
    map f := (F.map f.as).toLoc
    map_id X := by simp
    map₂ η := eqToHom (by rw [LocallyDiscrete.eq_of_hom η])
    mapComp f g := eqToHom (by simp) }

@[simp]
theorem Functor.toStrictlyUnitaryLaxFunctor_id :
    (𝟭 C).toStrictlyUnitaryLaxFunctor = StrictlyUnitaryLaxFunctor.id _ :=
  StrictlyUnitaryLaxFunctor.ext_of_isLocallyDiscrete (fun _ => rfl) (fun _ => HEq.rfl)

@[simp]
theorem Functor.toStrictlyUnitaryLaxFunctor_comp (F : C ⥤ D) (G : D ⥤ E) :
    (F ⋙ G).toStrictlyUnitaryLaxFunctor =
      F.toStrictlyUnitaryLaxFunctor.comp G.toStrictlyUnitaryLaxFunctor :=
  StrictlyUnitaryLaxFunctor.ext_of_isLocallyDiscrete (fun _ => rfl) (fun _ => HEq.rfl)

@[simps]
def StrictlyUnitaryLaxFunctor.equivFunctor :
    StrictlyUnitaryLaxFunctor (LocallyDiscrete C) (LocallyDiscrete D) ≃ (C ⥤ D) where
  toFun F :=
    { obj X := (F.obj ⟨X⟩).as
      map f := (F.map f.toLoc).as
      map_id X := congrArg Discrete.as (F.map_id ⟨X⟩)
      map_comp f g :=
        congrArg Discrete.as (LocallyDiscrete.eq_of_hom (F.mapComp f.toLoc g.toLoc)).symm }
  invFun G := G.toStrictlyUnitaryLaxFunctor
  left_inv _ :=
    StrictlyUnitaryLaxFunctor.ext_of_isLocallyDiscrete (fun _ => rfl) (fun _ => HEq.rfl)
  right_inv _ := rfl

end LocallyDiscrete

namespace Bicategory

variable (B : Type u) [Bicategory.{w, v} B]

def duskinNerve : SSet.{max u v w} where
  obj n := StrictlyUnitaryLaxFunctor (LocallyDiscrete (Fin (n.unop.len + 1))) B
  map θ := ↾fun F =>
    (SimplexCategory.toCat.map θ.unop).toFunctor.toStrictlyUnitaryLaxFunctor.comp F
  map_id _ := by
    ext F
    exact (congrArg (·.comp F) Functor.toStrictlyUnitaryLaxFunctor_id).trans
      (StrictlyUnitaryLaxFunctor.id_comp F)
  map_comp θ θ' := by
    ext F
    exact (congrArg (·.comp F) (Functor.toStrictlyUnitaryLaxFunctor_comp
      (SimplexCategory.toCat.map θ'.unop).toFunctor
      (SimplexCategory.toCat.map θ.unop).toFunctor)).trans
      (StrictlyUnitaryLaxFunctor.comp_assoc _ _ F)

theorem duskinNerve_obj (n : SimplexCategoryᵒᵖ) :
    (duskinNerve B).obj n =
      StrictlyUnitaryLaxFunctor (LocallyDiscrete (Fin (n.unop.len + 1))) B :=
  rfl

theorem duskinNerve_map {m n : SimplexCategoryᵒᵖ} (θ : m ⟶ n) (F : (duskinNerve B).obj m) :
    (duskinNerve B).map θ F =
      θ.unop.toOrderHom.monotone.functor.toStrictlyUnitaryLaxFunctor.comp F :=
  rfl

variable {B}

def duskinNerveMap {C : Type u} [Bicategory.{w, v} C] (G : StrictlyUnitaryLaxFunctor B C) :
    duskinNerve B ⟶ duskinNerve C where
  app _ := ↾fun F => F.comp G
  naturality _ _ _ := by
    ext F
    exact StrictlyUnitaryLaxFunctor.comp_assoc _ F G

@[simp]
theorem duskinNerveMap_app {C : Type u} [Bicategory.{w, v} C]
    (G : StrictlyUnitaryLaxFunctor B C) (n : SimplexCategoryᵒᵖ) (F : (duskinNerve B).obj n) :
    (duskinNerveMap G).app n F = F.comp G :=
  rfl

variable (B) in
theorem duskinNerveMap_id : duskinNerveMap (StrictlyUnitaryLaxFunctor.id B) = 𝟙 _ := by
  ext n F
  exact StrictlyUnitaryLaxFunctor.comp_id F

theorem duskinNerveMap_comp {C D : Type u} [Bicategory.{w, v} C] [Bicategory.{w, v} D]
    (G : StrictlyUnitaryLaxFunctor B C) (H : StrictlyUnitaryLaxFunctor C D) :
    duskinNerveMap (G.comp H) = duskinNerveMap G ≫ duskinNerveMap H := by
  ext n F
  exact (StrictlyUnitaryLaxFunctor.comp_assoc F G H).symm

def duskinNerveLocallyDiscreteIso (C : Type u) [Category.{v} C] :
    duskinNerve (LocallyDiscrete C) ≅ nerve C :=
  NatIso.ofComponents (fun _ => StrictlyUnitaryLaxFunctor.equivFunctor.toIso) fun _ => rfl

@[reassoc]
theorem duskinNerveLocallyDiscreteIso_hom_naturality {C D : Type u} [Category.{v} C]
    [Category.{v} D] (F : C ⥤ D) :
    duskinNerveMap F.toStrictlyUnitaryLaxFunctor ≫ (duskinNerveLocallyDiscreteIso D).hom =
      (duskinNerveLocallyDiscreteIso C).hom ≫ nerveMap F :=
  rfl

variable (B)

structure LaxComposable (n : ℕ) where
  obj : Fin (n + 1) → B
  hom (i j : Fin (n + 1)) (hij : i < j) : obj i ⟶ obj j
  cell (i j k : Fin (n + 1)) (hij : i < j) (hjk : j < k) :
    hom i j hij ≫ hom j k hjk ⟶ hom i k (hij.trans hjk)
  cocycle (i j k l : Fin (n + 1)) (hij : i < j) (hjk : j < k) (hkl : k < l) :
    cell i j k hij hjk ▷ hom k l hkl ≫ cell i k l (hij.trans hjk) hkl =
      (α_ _ _ _).hom ≫ hom i j hij ◁ cell j k l hjk hkl ≫ cell i j l hij (hjk.trans hkl)

namespace LaxComposable

variable {B} {n : ℕ}

@[ext]
theorem ext {L L' : LaxComposable B n} (h_obj : ∀ i, L.obj i = L'.obj i)
    (h_hom : ∀ i j hij, L.hom i j hij ≍ L'.hom i j hij)
    (h_cell : ∀ i j k hij hjk, L.cell i j k hij hjk ≍ L'.cell i j k hij hjk) : L = L' := by
  obtain ⟨obj, hom, cell, _⟩ := L
  obtain ⟨obj', hom', cell', _⟩ := L'
  obtain rfl : obj = obj' := funext h_obj
  obtain rfl : hom = hom' := by
    funext i j hij
    exact eq_of_heq (h_hom i j hij)
  obtain rfl : cell = cell' := by
    funext i j k hij hjk
    exact eq_of_heq (h_cell i j k hij hjk)
  rfl

variable (L : LaxComposable B n)

private def map (i j : Fin (n + 1)) (hij : i ≤ j) : L.obj i ⟶ L.obj j :=
  if h : i < j then L.hom i j h else eqToHom (congrArg L.obj (le_antisymm hij (not_lt.1 h)))

private theorem map_self (i : Fin (n + 1)) (hii : i ≤ i) : L.map i i hii = 𝟙 (L.obj i) := by
  rw [map, dif_neg (lt_irrefl i), eqToHom_refl]

private theorem map_of_lt (i j : Fin (n + 1)) (hij : i ≤ j) (h : i < j) :
    L.map i j hij = L.hom i j h :=
  dif_pos h

private def compLeft (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) (e : i = j) :
    L.map i j hij ≫ L.map j k hjk ⟶ L.map i k (hij.trans hjk) := by
  subst e
  exact eqToHom (by rw [L.map_self]) ≫ (λ_ _).hom

private def compRight (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) (e : j = k) :
    L.map i j hij ≫ L.map j k hjk ⟶ L.map i k (hij.trans hjk) := by
  subst e
  exact eqToHom (by rw [L.map_self]) ≫ (ρ_ _).hom

private def comp (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    L.map i j hij ≫ L.map j k hjk ⟶ L.map i k (hij.trans hjk) :=
  if h₁ : i < j then
    if h₂ : j < k then
      eqToHom (by rw [L.map_of_lt _ _ hij h₁, L.map_of_lt _ _ hjk h₂]) ≫ L.cell i j k h₁ h₂ ≫
        eqToHom (L.map_of_lt _ _ _ (h₁.trans h₂)).symm
    else L.compRight i j k hij hjk (le_antisymm hjk (not_lt.1 h₂))
  else L.compLeft i j k hij hjk (le_antisymm hij (not_lt.1 h₁))

private theorem comp_self_left (i k : Fin (n + 1)) (hii : i ≤ i) (hik : i ≤ k) :
    L.comp i i k hii hik = eqToHom (by rw [L.map_self]) ≫ (λ_ _).hom := by
  rw [comp, dif_neg (lt_irrefl i)]
  rfl

private theorem comp_self_right (i k : Fin (n + 1)) (hik : i ≤ k) (hkk : k ≤ k) (h : i < k) :
    L.comp i k k hik hkk = eqToHom (by rw [L.map_self]) ≫ (ρ_ _).hom := by
  rw [comp, dif_pos h, dif_neg (lt_irrefl k)]
  rfl

private theorem comp_of_lt (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) (h₁ : i < j)
    (h₂ : j < k) :
    L.comp i j k hij hjk = eqToHom (by rw [L.map_of_lt _ _ hij h₁, L.map_of_lt _ _ hjk h₂]) ≫
      L.cell i j k h₁ h₂ ≫ eqToHom (L.map_of_lt _ _ _ (h₁.trans h₂)).symm := by
  rw [comp, dif_pos h₁, dif_pos h₂]

variable {a b c d : B}

private theorem rightUnitor_aux {e : a ⟶ a} (he : e = 𝟙 a) (p : e ≫ 𝟙 a = e ≫ e)
    (q : e ≫ e = 𝟙 a ≫ e) : 𝟙 e = (ρ_ e).inv ≫ eqToHom p ≫ eqToHom q ≫ (λ_ e).hom := by
  subst he
  simp [unitors_equal]

private theorem associator_aux_left {e : a ⟶ a} (he : e = 𝟙 a) {g : a ⟶ b} {h : b ⟶ c}
    {k : a ⟶ c} (X : g ≫ h ⟶ k) (p : e ≫ g = 𝟙 a ≫ g) (q : e ≫ k = 𝟙 a ≫ k) :
    (eqToHom p ≫ (λ_ g).hom) ▷ h ≫ X ≫ 𝟙 k =
      (α_ e g h).hom ≫ e ◁ X ≫ eqToHom q ≫ (λ_ k).hom := by
  subst he
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  bicategory

private theorem associator_aux_middle {f : a ⟶ b} {e : b ⟶ b} (he : e = 𝟙 b) {h : b ⟶ c}
    {k : a ⟶ c} (X : f ≫ h ⟶ k) (p : f ≫ e = f ≫ 𝟙 b) (q : e ≫ h = 𝟙 b ≫ h) :
    (eqToHom p ≫ (ρ_ f).hom) ▷ h ≫ X ≫ 𝟙 k =
      (α_ f e h).hom ≫ f ◁ (eqToHom q ≫ (λ_ h).hom) ≫ X := by
  subst he
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  bicategory

private theorem associator_aux_right {f : a ⟶ b} {g : b ⟶ c} {e : c ⟶ c} (he : e = 𝟙 c)
    {k : a ⟶ c} (X : f ≫ g ⟶ k) (p : k ≫ e = k ≫ 𝟙 c) (q : g ≫ e = g ≫ 𝟙 c) :
    X ▷ e ≫ (eqToHom p ≫ (ρ_ k).hom) ≫ 𝟙 k =
      (α_ f g e).hom ≫ f ◁ (eqToHom q ≫ (ρ_ g).hom) ≫ X := by
  subst he
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  bicategory

private theorem associator_aux_cocycle {f₁ m₁ : a ⟶ b} {f₂ m₂ : b ⟶ c} {f₃ m₃ : c ⟶ d}
    {f₁₂ m₁₂ : a ⟶ c} {f₂₃ m₂₃ : b ⟶ d} {f₁₂₃ m₁₂₃ : a ⟶ d}
    (h₁ : m₁ = f₁) (h₂ : m₂ = f₂) (h₃ : m₃ = f₃)
    {θ₁₂ : f₁ ≫ f₂ ⟶ f₁₂} {θ₂₃ : f₂ ≫ f₃ ⟶ f₂₃} {θ₁₂₃ : f₁₂ ≫ f₃ ⟶ f₁₂₃}
    {θ₁₂₃' : f₁ ≫ f₂₃ ⟶ f₁₂₃}
    (hθ : θ₁₂ ▷ f₃ ≫ θ₁₂₃ = (α_ _ _ _).hom ≫ f₁ ◁ θ₂₃ ≫ θ₁₂₃')
    (p₁ : m₁ ≫ m₂ = f₁ ≫ f₂) (p₂ : f₁₂ = m₁₂) (p₃ : m₁₂ ≫ m₃ = f₁₂ ≫ f₃) (p₄ : f₁₂₃ = m₁₂₃)
    (p₅ : m₂ ≫ m₃ = f₂ ≫ f₃) (p₆ : f₂₃ = m₂₃) (p₇ : m₁ ≫ m₂₃ = f₁ ≫ f₂₃)
    (p₈ : f₁₂₃ = m₁₂₃) :
    (eqToHom p₁ ≫ θ₁₂ ≫ eqToHom p₂) ▷ m₃ ≫ (eqToHom p₃ ≫ θ₁₂₃ ≫ eqToHom p₄) ≫ 𝟙 _ =
      (α_ m₁ m₂ m₃).hom ≫ m₁ ◁ (eqToHom p₅ ≫ θ₂₃ ≫ eqToHom p₆) ≫
        (eqToHom p₇ ≫ θ₁₂₃' ≫ eqToHom p₈) := by
  subst h₁ h₂ h₃ p₂ p₄ p₆
  simpa using hθ

private def toFunctor : StrictlyUnitaryLaxFunctor (LocallyDiscrete (Fin (n + 1))) B :=
  .mk' {
    obj x := L.obj x.as
    map {x y} f := L.map x.as y.as (leOfHom f.as)
    map_id x := L.map_self x.as _
    map₂ _ := 𝟙 _
    map₂_id _ := rfl
    map₂_comp _ _ := (Category.comp_id _).symm
    mapComp f g := L.comp _ _ _ (leOfHom f.as) (leOfHom g.as)
    mapComp_naturality_left _ _ := by simp
    mapComp_naturality_right _ _ _ _ := by simp
    map₂_leftUnitor _ := by
      rw [L.comp_self_left]
      simp
    map₂_rightUnitor {x y} f := by
      rcases (leOfHom f.as).lt_or_eq with h | h
      · rw [L.comp_self_right _ _ _ _ h]
        simp
      · obtain rfl : x = y := LocallyDiscrete.ext h
        rw [L.comp_self_left]
        exact rightUnitor_aux (L.map_self _ _) _ _
    map₂_associator {x y z t} f g h := by
      rcases (leOfHom f.as).lt_or_eq with h₁ | h₁
      · rcases (leOfHom g.as).lt_or_eq with h₂ | h₂
        · rcases (leOfHom h.as).lt_or_eq with h₃ | h₃
          · rw [L.comp_of_lt _ _ _ _ _ h₁ h₂, L.comp_of_lt _ _ _ _ _ (h₁.trans h₂) h₃,
              L.comp_of_lt _ _ _ _ _ h₂ h₃, L.comp_of_lt _ _ _ _ _ h₁ (h₂.trans h₃)]
            exact associator_aux_cocycle (L.map_of_lt _ _ _ h₁) (L.map_of_lt _ _ _ h₂)
              (L.map_of_lt _ _ _ h₃) (L.cocycle _ _ _ _ h₁ h₂ h₃) _ _ _ _ _ _ _ _
          · obtain rfl : z = t := LocallyDiscrete.ext h₃
            rw [L.comp_self_right _ _ _ _ (h₁.trans h₂), L.comp_self_right _ _ _ _ h₂]
            exact associator_aux_right (L.map_self _ _) _ _ _
        · obtain rfl : y = z := LocallyDiscrete.ext h₂
          rw [L.comp_self_right _ _ _ _ h₁, L.comp_self_left]
          exact associator_aux_middle (L.map_self _ _) _ _ _
      · obtain rfl : x = y := LocallyDiscrete.ext h₁
        rw [L.comp_self_left, L.comp_self_left]
        exact associator_aux_left (L.map_self _ _) _ _ _ }

end LaxComposable

def duskinNerveSimplexEquiv (n : ℕ) : (duskinNerve B) _⦋n⦌ ≃ LaxComposable B n where
  toFun F :=
    { obj i := F.obj ⟨i⟩
      hom i j hij := F.map (homOfLE hij.le).toLoc
      cell i j k hij hjk := F.mapComp (homOfLE hij.le).toLoc (homOfLE hjk.le).toLoc
      cocycle i j k l hij hjk hkl := by
        have h := F.map₂_associator (homOfLE hij.le).toLoc (homOfLE hjk.le).toLoc
          (homOfLE hkl.le).toLoc
        rw [(Subsingleton.elim _ _ : (α_ (homOfLE hij.le).toLoc (homOfLE hjk.le).toLoc
          (homOfLE hkl.le).toLoc).hom = 𝟙 _), PrelaxFunctor.map₂_id, Category.comp_id] at h
        exact h }
  invFun L := L.toFunctor
  left_inv _ := StrictlyUnitaryLaxFunctor.ext_of_lt (fun _ => rfl)
    (fun _ h => heq_of_eq (LaxComposable.map_of_lt _ _ _ h.le h))
    (fun _ _ h₁ h₂ => (heq_of_eq (LaxComposable.comp_of_lt _ _ _ _ _ _ h₁ h₂)).trans
      (eqToHom_conj_heq _ _ _))
  right_inv _ := LaxComposable.ext (fun _ => rfl)
    (fun _ _ h => heq_of_eq (LaxComposable.map_of_lt _ _ _ h.le h))
    (fun _ _ _ h₁ h₂ => (heq_of_eq (LaxComposable.comp_of_lt _ _ _ _ _ _ h₁ h₂)).trans
      (eqToHom_conj_heq _ _ _))

@[simp]
theorem duskinNerveSimplexEquiv_obj (n : ℕ) (F : (duskinNerve B) _⦋n⦌) (i : Fin (n + 1)) :
    (duskinNerveSimplexEquiv B n F).obj i = F.obj ⟨i⟩ :=
  rfl

@[simp]
theorem duskinNerveSimplexEquiv_hom (n : ℕ) (F : (duskinNerve B) _⦋n⦌) (i j : Fin (n + 1))
    (hij : i < j) :
    (duskinNerveSimplexEquiv B n F).hom i j hij = F.map (homOfLE hij.le).toLoc :=
  rfl

@[simp]
theorem duskinNerveSimplexEquiv_cell (n : ℕ) (F : (duskinNerve B) _⦋n⦌) (i j k : Fin (n + 1))
    (hij : i < j) (hjk : j < k) :
    (duskinNerveSimplexEquiv B n F).cell i j k hij hjk =
      F.mapComp (homOfLE hij.le).toLoc (homOfLE hjk.le).toLoc :=
  rfl

def duskinNerveVertexEquiv : (duskinNerve B) _⦋0⦌ ≃ B :=
  (duskinNerveSimplexEquiv B 0).trans
    { toFun L := L.obj 0
      invFun b :=
        { obj _ := b
          hom _ _ hij := (hij.ne (Fin.ext (by omega))).elim
          cell _ _ _ hij _ := (hij.ne (Fin.ext (by omega))).elim
          cocycle _ _ _ _ hij _ _ := (hij.ne (Fin.ext (by omega))).elim }
      left_inv L := LaxComposable.ext (fun _ => congrArg L.obj (Fin.ext (by omega)))
        (fun _ _ hij => (hij.ne (Fin.ext (by omega))).elim)
        (fun _ _ _ hij _ => (hij.ne (Fin.ext (by omega))).elim)
      right_inv _ := rfl }

@[simp]
theorem duskinNerveVertexEquiv_apply (F : (duskinNerve B) _⦋0⦌) :
    duskinNerveVertexEquiv B F = F.obj ⟨0⟩ :=
  rfl

private theorem eq_zero_of_lt {i j : Fin 2} (hij : i < j) : i = 0 := by
  rw [Fin.lt_def] at hij
  ext
  simp only [Fin.val_zero]
  omega

private theorem eq_one_of_lt {i j : Fin 2} (hij : i < j) : j = 1 := by
  rw [Fin.lt_def] at hij
  ext
  simp only [Fin.val_one]
  omega

private theorem not_lt_lt {i j k : Fin 2} (hij : i < j) (hjk : j < k) : False := by
  rw [Fin.lt_def] at hij hjk
  omega

private def edgeHom {a b : B} (f : a ⟶ b) (i j : Fin 2) (hij : i < j) :
    (![a, b] : Fin 2 → B) i ⟶ (![a, b] : Fin 2 → B) j := by
  obtain rfl := eq_zero_of_lt hij
  obtain rfl := eq_one_of_lt hij
  exact f

def duskinNerveEdgeEquiv : (duskinNerve B) _⦋1⦌ ≃ Σ (a b : B), (a ⟶ b) :=
  (duskinNerveSimplexEquiv B 1).trans
    { toFun L := ⟨L.obj 0, L.obj 1, L.hom 0 1 Fin.zero_lt_one⟩
      invFun f :=
        { obj := ![f.1, f.2.1]
          hom := edgeHom B f.2.2
          cell _ _ _ hij hjk := (not_lt_lt hij hjk).elim
          cocycle _ _ _ _ hij hjk _ := (not_lt_lt hij hjk).elim }
      left_inv L := LaxComposable.ext (fun i => by fin_cases i <;> rfl)
        (fun i j hij => by
          obtain rfl := eq_zero_of_lt hij
          obtain rfl := eq_one_of_lt hij
          rfl)
        (fun _ _ _ hij hjk => (not_lt_lt hij hjk).elim)
      right_inv _ := rfl }

@[simp]
theorem duskinNerveEdgeEquiv_apply (F : (duskinNerve B) _⦋1⦌) :
    duskinNerveEdgeEquiv B F = ⟨F.obj ⟨0⟩, F.obj ⟨1⟩, F.map (homOfLE Fin.zero_lt_one.le).toLoc⟩ :=
  rfl

end Bicategory

end CategoryTheory
