import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

universe s t u v w

namespace CategoryTheory

open Opposite

namespace CategoryOfElements

variable {C : Type v} [Category.{w} C] {F : Cᵒᵖ ⥤ Type t}

@[simps obj]
def fromOver {a : C} (x : F.obj (op a)) : (Over a)ᵒᵖ ⥤ F.Elements where
  obj f := ⟨op f.unop.left, F.map f.unop.hom.op x⟩
  map {f g} k := ⟨k.unop.left.op, by
    dsimp
    rw [← Functor.map_comp_apply, ← op_comp, Over.w]⟩
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

@[simp]
theorem π_obj_fromOver_obj {a : C} (x : F.obj (op a)) (f : (Over a)ᵒᵖ) :
    (π F).obj ((fromOver x).obj f) = op f.unop.left :=
  rfl

@[simp]
theorem fromOver_map_val {a : C} (x : F.obj (op a)) {f g : (Over a)ᵒᵖ} (k : f ⟶ g) :
    ((fromOver x).map k).val = k.unop.left.op :=
  rfl

private theorem elementsMk_eq {c : Cᵒᵖ} {x y : F.obj c} (h : x = y) :
    F.elementsMk c x = F.elementsMk c y :=
  h ▸ rfl

private theorem eqToHom_val {p q : F.Elements} (h : p = q) :
    (eqToHom h).val = eqToHom (congrArg (π F).obj h) := by
  subst h
  rfl

private theorem eqToHom_val_mk {c : Cᵒᵖ} {x y : F.obj c}
    (h : F.elementsMk c x = F.elementsMk c y) : (eqToHom h).val = 𝟙 c := by
  cases h
  rfl

private theorem functor_ext {D : Type*} [Category D] {G₁ G₂ : D ⥤ F.Elements}
    (hobj : ∀ X, G₁.obj X = G₂.obj X) (hπ : G₁ ⋙ π F = G₂ ⋙ π F) : G₁ = G₂ :=
  Functor.ext hobj fun X Y f ↦ by
    apply (π F).map_injective
    have := Functor.congr_hom hπ f
    simp only [Functor.comp_map] at this
    rw [this, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]

theorem map_op_comp_fromOver {a b : C} (f : b ⟶ a) (x : F.obj (op a)) :
    (Over.map f).op ⋙ fromOver x = fromOver (F.map f.op x) :=
  functor_ext (fun g ↦ elementsMk_eq (by simp [← Functor.map_comp_apply, ← op_comp])) rfl

theorem fromOver_comp_map {G : Cᵒᵖ ⥤ Type t} (α : F ⟶ G) {a : C} (x : F.obj (op a)) :
    fromOver x ⋙ map α = fromOver (α.app (op a) x) :=
  functor_ext (fun g ↦ elementsMk_eq ((NatTrans.naturality_apply α g.unop.hom.op x))) rfl

section Total

variable {F : Cᵒᵖ ⥤ Type (max t s)}

private theorem map_heq_map (G : F.Elements ⥤ Type s) {p : F.Elements} {c : Cᵒᵖ}
    {y y' : F.obj c} (φ : p ⟶ F.elementsMk c y) (ψ : p ⟶ F.elementsMk c y') (h : φ.val = ψ.val)
    (e : G.obj p) : HEq (G.map φ e) (G.map ψ e) := by
  obtain rfl : y = y' := φ.2.symm.trans (h ▸ ψ.2)
  obtain rfl : φ = ψ := CategoryOfElements.ext _ _ _ h
  rfl

def total (G : F.Elements ⥤ Type s) : Cᵒᵖ ⥤ Type (max t s) where
  obj c := Σ x : F.obj c, G.obj (F.elementsMk c x)
  map {c d} f := ↾fun p ↦ ⟨F.map f p.1,
    G.map (homMk (F.elementsMk c p.1) (F.elementsMk d (F.map f p.1)) f rfl) p.2⟩
  map_id c := ConcreteCategory.hom_ext _ _ fun ⟨x, e⟩ ↦ by
    refine Sigma.ext (β := fun x ↦ G.obj (F.elementsMk c x)) (Functor.map_id_apply F c x) ?_
    exact (map_heq_map G (homMk (F.elementsMk c x) (F.elementsMk c (F.map (𝟙 c) x)) (𝟙 c) rfl)
      (𝟙 _) rfl e).trans (heq_of_eq (Functor.map_id_apply G _ e))
  map_comp {c d d'} f g := ConcreteCategory.hom_ext _ _ fun ⟨x, e⟩ ↦
    Sigma.ext (β := fun x ↦ G.obj (F.elementsMk d' x)) (Functor.map_comp_apply F f g x)
      ((map_heq_map G
        (homMk (F.elementsMk c x) (F.elementsMk d' (F.map (f ≫ g) x)) (f ≫ g) rfl)
        (homMk (F.elementsMk c x) (F.elementsMk d (F.map f x)) f rfl ≫
          homMk _ (F.elementsMk d' (F.map g (F.map f x))) g rfl) rfl e).trans
        (heq_of_eq (Functor.map_comp_apply G _ _ e)))

def totalπ (G : F.Elements ⥤ Type s) : total G ⟶ F where
  app c := ↾fun p ↦ p.1

@[simp]
theorem totalπ_app (G : F.Elements ⥤ Type s) (c : Cᵒᵖ) (p : (total G).obj c) :
    (totalπ G).app c p = p.1 :=
  rfl

def totalMap {F' : Cᵒᵖ ⥤ Type (max t s)} (α : F ⟶ F') (G : F'.Elements ⥤ Type s) :
    total (map α ⋙ G) ⟶ total G where
  app c := ↾fun p ↦ ⟨α.app c p.1, p.2⟩
  naturality c d f := ConcreteCategory.hom_ext _ _ fun ⟨x, e⟩ ↦ by
    refine Sigma.ext (β := fun y ↦ G.obj (F'.elementsMk d y)) ?_ ?_
    · exact NatTrans.naturality_apply α f x
    · exact map_heq_map G
        ((map α).map (homMk (F.elementsMk c x) (F.elementsMk d (F.map f x)) f rfl))
        (homMk (F'.elementsMk c (α.app c x)) (F'.elementsMk d (F'.map f (α.app c x))) f rfl) rfl e

@[simp]
theorem totalMap_app {F' : Cᵒᵖ ⥤ Type (max t s)} (α : F ⟶ F') (G : F'.Elements ⥤ Type s) (c : Cᵒᵖ)
    (p : (total (map α ⋙ G)).obj c) : (totalMap α G).app c p = ⟨α.app c p.1, p.2⟩ :=
  rfl

theorem isPullback_totalMap {F' : Cᵒᵖ ⥤ Type (max t s)} (α : F ⟶ F') (G : F'.Elements ⥤ Type s) :
    IsPullback (totalMap α G) (totalπ (map α ⋙ G)) (totalπ G) α := by
  refine IsPullback.of_forall_isPullback_app fun c ↦ 
    (Limits.Types.isPullback_iff _ _ _ _).2 ⟨rfl, ?_, ?_⟩
  · rintro ⟨x, e⟩ ⟨x', e'⟩ ⟨h₁, h₂⟩
    obtain rfl : x = x' := h₂
    obtain ⟨-, h⟩ := Sigma.mk.inj_iff.1 h₁
    obtain rfl : e = e' := eq_of_heq h
    rfl
  · rintro ⟨y, e⟩ x (rfl : y = α.app c x)
    exact ⟨⟨x, e⟩, rfl, rfl⟩

section Fibres

variable {E : Cᵒᵖ ⥤ Type (max t s)} (p : E ⟶ F) [∀ c x, Small.{s} {e : E.obj c // p.app c e = x}]

noncomputable def fibres : F.Elements ⥤ Type s where
  obj y := Shrink.{s} {e : E.obj y.1 // p.app y.1 e = y.2}
  map {y z} φ := ↾fun r ↦ equivShrink _ ⟨E.map φ.val ((equivShrink _).symm r).1, by
    rw [NatTrans.naturality_apply, ((equivShrink _).symm r).2, φ.2]⟩
  map_id y := ConcreteCategory.hom_ext _ _ fun r ↦ (equivShrink _).symm.injective (by
    apply Subtype.ext
    simp)
  map_comp φ ψ := ConcreteCategory.hom_ext _ _ fun r ↦ (equivShrink _).symm.injective (by
    apply Subtype.ext
    simp)

noncomputable def totalFibresIso : total (fibres p) ≅ E :=
  NatIso.ofComponents (fun c ↦ ((Equiv.sigmaCongrRight fun _ ↦ (equivShrink _).symm).trans
    (Equiv.sigmaFiberEquiv (p.app c))).toIso) fun _ ↦ ConcreteCategory.hom_ext _ _ fun _ ↦
      congrArg Subtype.val ((equivShrink _).symm_apply_apply _)

@[reassoc (attr := simp)]
theorem totalFibresIso_hom_comp : (totalFibresIso p).hom ≫ p = totalπ (fibres p) := by
  ext c ⟨x, r⟩
  exact ((equivShrink _).symm r).2

end Fibres

end Total

end CategoryOfElements

variable (A : Type v) [Category.{w} A]

def presheafUniverse : Aᵒᵖ ⥤ Type (max v w (u + 1)) where
  obj a := (Over a.unop)ᵒᵖ ⥤ Type u
  map f := ↾fun P ↦ (Over.map f.unop).op ⋙ P
  map_id a := by
    ext P
    dsimp
    rw [Over.mapId_eq]
    rfl
  map_comp f g := by
    ext P
    dsimp
    rw [Over.mapComp_eq]
    rfl

theorem presheafUniverse_obj (a : Aᵒᵖ) :
    (presheafUniverse.{u} A).obj a = ((Over a.unop)ᵒᵖ ⥤ Type u) :=
  rfl

@[simp]
theorem presheafUniverse_map_apply {a b : Aᵒᵖ} (f : a ⟶ b) (P : (presheafUniverse.{u} A).obj a) :
    (presheafUniverse.{u} A).map f P = (Over.map f.unop).op ⋙ P :=
  rfl

variable {A} in
def Over.homToId {a b : A} (f : b ⟶ a) : (Over.map f).obj (Over.mk (𝟙 b)) ⟶ Over.mk (𝟙 a) :=
  Over.homMk f (by simp)

private theorem eqToHom_eq_map {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type u) {X Y : C}
    (h : P.obj (op X) = P.obj (op Y)) (hXY : Y = X) :
    eqToHom h = P.map (eqToHom hXY).op := by
  subst hXY
  simp

def presheafUniverseFamilyMap {a b : A} (f : b ⟶ a) (P : (Over a)ᵒᵖ ⥤ Type u)
    (Q : (Over b)ᵒᵖ ⥤ Type u) (h : (Over.map f).op ⋙ P = Q) :
    P.obj (op (Over.mk (𝟙 a))) ⟶ Q.obj (op (Over.mk (𝟙 b))) :=
  P.map (Over.homToId f).op ≫ eqToHom (by rw [← h]; rfl)

private theorem familyMap_id {a : A} (P : (Over a)ᵒᵖ ⥤ Type u) (h : (Over.map (𝟙 a)).op ⋙ P = P) :
    presheafUniverseFamilyMap A (𝟙 a) P P h = 𝟙 _ := by
  rw [presheafUniverseFamilyMap]
  rw [eqToHom_eq_map P _ (by rw [Over.mapId_eq]; rfl :
    Over.mk (𝟙 a) = (Over.map (𝟙 a)).obj (Over.mk (𝟙 a)))]
  rw [← P.map_comp, ← op_comp, ← P.map_id, ← op_id]
  congr 1
  apply Quiver.Hom.unop_inj
  ext
  simp [Over.homToId]

private theorem familyMap_comp {a b c : A} (f : b ⟶ a) (g : c ⟶ b) (P : (Over a)ᵒᵖ ⥤ Type u)
    (Q : (Over b)ᵒᵖ ⥤ Type u) (R : (Over c)ᵒᵖ ⥤ Type u) (hf : (Over.map f).op ⋙ P = Q)
    (hg : (Over.map g).op ⋙ Q = R) (hgf : (Over.map (g ≫ f)).op ⋙ P = R) :
    presheafUniverseFamilyMap A (g ≫ f) P R hgf =
      presheafUniverseFamilyMap A f P Q hf ≫ presheafUniverseFamilyMap A g Q R hg := by
  subst hf hg
  simp only [presheafUniverseFamilyMap, Functor.comp_obj, Functor.op_obj, unop_op,
    Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, eqToHom_refl, Category.comp_id]
  rw [eqToHom_eq_map P _ (by rw [Over.mapComp_eq]; rfl :
    (Over.map f).obj ((Over.map g).obj (Over.mk (𝟙 c))) = (Over.map (g ≫ f)).obj (Over.mk (𝟙 c))),
    ← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  ext
  simp [Over.homToId]

private theorem eqToHom_eq_map' {D : Type*} [Category D] (G : D ⥤ Type u) {p q : D}
    (h : G.obj p = G.obj q) (e : p = q) : eqToHom h = G.map (eqToHom e) := by
  subst e
  simp

private theorem eqToHom_comp_map_comp_eqToHom' {D : Type*} [Category D] (G : D ⥤ Type u)
    {p p' q q' : D} (k : p ⟶ q) (h₁ : G.obj p' = G.obj p) (h₂ : G.obj q = G.obj q') (e₁ : p' = p)
    (e₂ : q = q') : eqToHom h₁ ≫ G.map k ≫ eqToHom h₂ = G.map (eqToHom e₁ ≫ k ≫ eqToHom e₂) := by
  subst e₁ e₂
  simp

private theorem eqToHom_comp_map_comp_eqToHom {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type u)
    {X X' Y Y' : C} (k : Y ⟶ X) (h₁ : P.obj (op X') = P.obj (op X))
    (h₂ : P.obj (op Y) = P.obj (op Y')) (e₁ : X = X') (e₂ : Y' = Y) :
    eqToHom h₁ ≫ P.map k.op ≫ eqToHom h₂ = P.map (eqToHom e₂ ≫ k ≫ eqToHom e₁).op := by
  subst e₁ e₂
  simp

def presheafUniverseFamily : (presheafUniverse.{u} A).Elements ⥤ Type u where
  obj x := (x.2 : (Over x.1.unop)ᵒᵖ ⥤ Type u).obj (op (Over.mk (𝟙 x.1.unop)))
  map {x y} f := presheafUniverseFamilyMap A f.1.unop x.2 y.2 f.2
  map_id x := familyMap_id A x.2 _
  map_comp {x y z} f g := familyMap_comp A _ _ x.2 y.2 z.2 f.2 g.2 _

@[simp]
theorem presheafUniverseFamily_obj (x : (presheafUniverse.{u} A).Elements) :
    (presheafUniverseFamily A).obj x =
      (x.2 : (Over x.1.unop)ᵒᵖ ⥤ Type u).obj (op (Over.mk (𝟙 x.1.unop))) :=
  rfl

@[simp]
theorem presheafUniverseFamily_map {x y : (presheafUniverse.{u} A).Elements} (f : x ⟶ y) :
    (presheafUniverseFamily A).map f = presheafUniverseFamilyMap A f.1.unop x.2 y.2 f.2 :=
  rfl

private theorem familyMap_restrict {a b c : A} (φ : b ⟶ a) (κ : c ⟶ b) (ψ : c ⟶ a)
    (hκ : κ ≫ φ = ψ) (P : (Over a)ᵒᵖ ⥤ Type u)
    (h : (Over.map κ).op ⋙ (Over.map φ).op ⋙ P = (Over.map ψ).op ⋙ P) :
    presheafUniverseFamilyMap A κ ((Over.map φ).op ⋙ P) ((Over.map ψ).op ⋙ P) h =
      P.map (Over.homMk κ (by simp [hκ]) :
        (Over.map ψ).obj (Over.mk (𝟙 c)) ⟶ (Over.map φ).obj (Over.mk (𝟙 b))).op := by
  subst hκ
  simp only [presheafUniverseFamilyMap, Functor.comp_obj, Functor.op_obj, unop_op,
    Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op]
  rw [eqToHom_eq_map P _ (congrArg Over.mk (by simp) :
    (Over.map (κ ≫ φ)).obj (Over.mk (𝟙 c)) = (Over.map φ).obj ((Over.map κ).obj (Over.mk (𝟙 c)))),
    ← P.map_comp, ← op_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  ext
  simp [Over.homToId]

open CategoryOfElements in
theorem fromOver_comp_presheafUniverseFamily {a : A} (P : (Over a)ᵒᵖ ⥤ Type u) :
    fromOver (F := presheafUniverse.{u} A) P ⋙ presheafUniverseFamily A = P :=
  Functor.ext (fun g ↦ congrArg P.obj (congrArg op
      (congrArg Over.mk (Category.id_comp g.unop.hom) :
        (Over.map g.unop.hom).obj (Over.mk (𝟙 g.unop.left)) = g.unop)))
    (fun g g' k ↦ by
      obtain ⟨g⟩ := g
      obtain ⟨g'⟩ := g'
      obtain ⟨k⟩ := k
      obtain ⟨Y, φ, rfl⟩ := Over.mk_surjective g
      obtain ⟨Y', φ', rfl⟩ := Over.mk_surjective g'
      obtain ⟨κ, hκ, rfl⟩ := Over.homMk_surjective k
      refine (familyMap_restrict A φ κ φ' hκ P
        ((fromOver (F := presheafUniverse.{u} A) P).map (Over.homMk κ hκ).op).2).trans
        (Eq.trans ?_ (eqToHom_comp_map_comp_eqToHom P (Over.homMk κ hκ) _ _
          (congrArg Over.mk (by simp)) (congrArg Over.mk (by simp))).symm)
      congr 1
      apply Quiver.Hom.unop_inj
      ext
      simp)

open CategoryOfElements in
def presheafUniverseEquiv (F : Aᵒᵖ ⥤ Type (max v w (u + 1))) :
    (F.Elements ⥤ Type u) ≃ (F ⟶ presheafUniverse.{u} A) where
  toFun G :=
    { app a := ↾fun x ↦ fromOver (a := a.unop) x ⋙ G
      naturality a b f := by
        ext x
        exact congrArg (· ⋙ G) (map_op_comp_fromOver f.unop x).symm }
  invFun χ := map χ ⋙ presheafUniverseFamily A
  left_inv G := Functor.ext
    (fun x ↦ congrArg G.obj (elementsMk_eq (by simp) :
      F.elementsMk x.1 (F.map (𝟙 x.1.unop).op x.2) = F.elementsMk x.1 x.2))
    (fun ⟨⟨a⟩, x⟩ ⟨⟨b⟩, y⟩ f ↦ by
      obtain ⟨⟨f⟩, hf⟩ := f
      refine (congrArg (G.map ((fromOver x).map (Over.homToId f).op) ≫ ·)
        (eqToHom_eq_map' G _ (elementsMk_eq
          (by rw [Category.id_comp, op_id, Functor.map_id]; exact hf) :
          F.elementsMk (op b) (F.map (𝟙 b ≫ f).op x) =
            F.elementsMk (op b) (F.map (𝟙 b).op y)))).trans ?_
      refine (G.map_comp _ _).symm.trans (Eq.trans ?_ (eqToHom_comp_map_comp_eqToHom' G _ _ _
        (elementsMk_eq (by simp) :
          F.elementsMk (op a) (F.map (𝟙 a).op x) = F.elementsMk (op a) x)
        (elementsMk_eq (by simp) :
          F.elementsMk (op b) y = F.elementsMk (op b) (F.map (𝟙 b).op y))).symm)
      congr 1
      ext
      refine comp_val.trans ?_
      refine (congrArg (_ ≫ ·) (eqToHom_val_mk _)).trans ?_
      refine Eq.trans ?_ (congrArg (· ≫ _) (eqToHom_val_mk _)).symm
      refine Eq.trans ?_ (congrArg (_ ≫ _ ≫ ·) (eqToHom_val_mk _)).symm
      exact (Category.comp_id _).trans
        ((Category.id_comp _).symm.trans (congrArg (_ ≫ ·) (Category.comp_id _).symm)))
  right_inv χ := by
    ext ⟨a⟩ x
    refine (congrArg (· ⋙ presheafUniverseFamily A) (fromOver_comp_map χ x)).trans ?_
    exact fromOver_comp_presheafUniverseFamily A _

theorem presheafUniverseEquiv_symm_apply (F : Aᵒᵖ ⥤ Type (max v w (u + 1)))
    (χ : F ⟶ presheafUniverse.{u} A) :
    (presheafUniverseEquiv A F).symm χ = CategoryOfElements.map χ ⋙ presheafUniverseFamily A :=
  rfl

@[simp]
theorem presheafUniverseEquiv_apply_app (F : Aᵒᵖ ⥤ Type (max v w (u + 1)))
    (G : F.Elements ⥤ Type u) (a : Aᵒᵖ) (x : F.obj a) :
    (presheafUniverseEquiv A F G).app a x = CategoryOfElements.fromOver (a := a.unop) x ⋙ G :=
  rfl

theorem presheafUniverseEquiv_naturality {F G : Aᵒᵖ ⥤ Type (max v w (u + 1))} (g : G ⟶ F)
    (P : F.Elements ⥤ Type u) :
    presheafUniverseEquiv A G (CategoryOfElements.map g ⋙ P) =
      g ≫ presheafUniverseEquiv A F P := by
  rw [← Equiv.eq_symm_apply, presheafUniverseEquiv_symm_apply]
  conv_lhs => rw [← (presheafUniverseEquiv A F).symm_apply_apply P,
    presheafUniverseEquiv_symm_apply]
  rfl

def presheafUniverseTotal : Aᵒᵖ ⥤ Type (max v w (u + 1)) :=
  CategoryOfElements.total.{u, max v w (u + 1)} (presheafUniverseFamily.{u} A)

def presheafUniverseTotalπ : presheafUniverseTotal.{u} A ⟶ presheafUniverse.{u} A :=
  CategoryOfElements.totalπ.{u, max v w (u + 1)} (presheafUniverseFamily.{u} A)

open CategoryOfElements in
theorem exists_isPullback_presheafUniverseTotalπ {E F : Aᵒᵖ ⥤ Type (max v w (u + 1))} (p : E ⟶ F)
    (hp : ∀ (a : Aᵒᵖ) (x : F.obj a), Small.{u} {e : E.obj a // p.app a e = x}) :
    ∃ (χ : F ⟶ presheafUniverse.{u} A) (q : E ⟶ presheafUniverseTotal.{u} A),
      IsPullback q p (presheafUniverseTotalπ A) χ := by
  let χ := presheafUniverseEquiv A F (fibres.{u, max v w (u + 1)} p)
  have hG : map χ ⋙ presheafUniverseFamily A = fibres.{u, max v w (u + 1)} p :=
    (presheafUniverseEquiv A F).symm_apply_apply _
  obtain ⟨e, he⟩ : ∃ e : total.{u, max v w (u + 1)} (map χ ⋙ presheafUniverseFamily A) ≅ E,
      e.hom ≫ p = totalπ.{u, max v w (u + 1)} _ := by
    rw [hG]
    exact ⟨totalFibresIso p, totalFibresIso_hom_comp p⟩
  exact ⟨χ, e.inv ≫ totalMap.{u, max v w (u + 1)} χ _,
    (isPullback_totalMap.{u, max v w (u + 1)} χ (presheafUniverseFamily A)).of_iso e
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ((Category.comp_id _).trans (e.hom_inv_id_assoc _).symm)
    ((Category.comp_id _).trans he.symm) ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)⟩

end CategoryTheory
