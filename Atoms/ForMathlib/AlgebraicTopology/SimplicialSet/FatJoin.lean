import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CommaCone
import Atoms.ForMathlib.CategoryTheory.Adhesive.Basic
import Atoms.ForMathlib.CategoryTheory.Limits.FunctorToTypes
import Atoms.ForMathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
import Mathlib.CategoryTheory.Adjunction.Unique

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory Simplicial
  Opposite

universe u

namespace SSet

section FatJoin

variable (X Y : SSet.{u})

noncomputable def fatJoinBoundaryMap : (∂Δ[1] : SSet.{u}) ⊗ (X ⊗ Y) ⟶ X ⨿ Y :=
  boundaryOneTensorDesc (fst X Y ≫ coprod.inl) (snd X Y ≫ coprod.inr)

noncomputable def fatJoin : SSet.{u} :=
  pushout (fatJoinBoundaryMap X Y) ((∂Δ[1]).ι ▷ (X ⊗ Y))

noncomputable def fatJoinIncl : X ⨿ Y ⟶ fatJoin X Y :=
  pushout.inl (fatJoinBoundaryMap X Y) ((∂Δ[1]).ι ▷ (X ⊗ Y))

noncomputable def fatJoinCyl : Δ[1] ⊗ (X ⊗ Y) ⟶ fatJoin X Y :=
  pushout.inr (fatJoinBoundaryMap X Y) ((∂Δ[1]).ι ▷ (X ⊗ Y))

theorem isPushout_fatJoin :
    IsPushout (fatJoinBoundaryMap X Y) ((∂Δ[1]).ι ▷ (X ⊗ Y)) (fatJoinIncl X Y) (fatJoinCyl X Y) :=
  IsPushout.of_hasPushout _ _

noncomputable def fatJoinInclLeft : X ⟶ fatJoin X Y :=
  coprod.inl ≫ fatJoinIncl X Y

noncomputable def fatJoinInclRight : Y ⟶ fatJoin X Y :=
  coprod.inr ≫ fatJoinIncl X Y

@[reassoc]
theorem stdSimplex_δ_one_whiskerRight_fatJoinCyl :
    stdSimplex.δ 1 ▷ (X ⊗ Y) ≫ fatJoinCyl X Y = snd _ _ ≫ fst X Y ≫ fatJoinInclLeft X Y := by
  rw [← boundary.ι_ι, comp_whiskerRight, Category.assoc, ← (isPushout_fatJoin X Y).w,
    fatJoinBoundaryMap, boundary_ι_one_whiskerRight_boundaryOneTensorDesc_assoc, fatJoinInclLeft]
  simp only [Category.assoc]

@[reassoc]
theorem stdSimplex_δ_zero_whiskerRight_fatJoinCyl :
    stdSimplex.δ 0 ▷ (X ⊗ Y) ≫ fatJoinCyl X Y = snd _ _ ≫ snd X Y ≫ fatJoinInclRight X Y := by
  rw [← boundary.ι_ι, comp_whiskerRight, Category.assoc, ← (isPushout_fatJoin X Y).w,
    fatJoinBoundaryMap, boundary_ι_zero_whiskerRight_boundaryOneTensorDesc_assoc,
    fatJoinInclRight]
  simp only [Category.assoc]

variable {X Y}

theorem fatJoin_hom_ext {Z : SSet.{u}} {f g : fatJoin X Y ⟶ Z}
    (hl : fatJoinInclLeft X Y ≫ f = fatJoinInclLeft X Y ≫ g)
    (hr : fatJoinInclRight X Y ≫ f = fatJoinInclRight X Y ≫ g)
    (hc : fatJoinCyl X Y ≫ f = fatJoinCyl X Y ≫ g) : f = g := by
  rw [fatJoinInclLeft, Category.assoc, Category.assoc] at hl
  rw [fatJoinInclRight, Category.assoc, Category.assoc] at hr
  exact (isPushout_fatJoin X Y).hom_ext (coprod.hom_ext hl hr) hc

noncomputable def fatJoinDesc {Z : SSet.{u}} (a : X ⟶ Z) (b : Y ⟶ Z) (h : Δ[1] ⊗ (X ⊗ Y) ⟶ Z)
    (h₀ : stdSimplex.δ 1 ▷ (X ⊗ Y) ≫ h = snd _ _ ≫ fst X Y ≫ a)
    (h₁ : stdSimplex.δ 0 ▷ (X ⊗ Y) ≫ h = snd _ _ ≫ snd X Y ≫ b) : fatJoin X Y ⟶ Z :=
  (isPushout_fatJoin X Y).desc (coprod.desc a b) h (boundaryOneTensor_hom_ext
    (by
      rw [fatJoinBoundaryMap, boundary_ι_one_whiskerRight_boundaryOneTensorDesc_assoc,
        ← comp_whiskerRight_assoc, boundary.ι_ι, h₀]
      simp only [Category.assoc, coprod.inl_desc])
    (by
      rw [fatJoinBoundaryMap, boundary_ι_zero_whiskerRight_boundaryOneTensorDesc_assoc,
        ← comp_whiskerRight_assoc, boundary.ι_ι, h₁]
      simp only [Category.assoc, coprod.inr_desc]))

section Desc

variable {Z : SSet.{u}} (a : X ⟶ Z) (b : Y ⟶ Z) (h : Δ[1] ⊗ (X ⊗ Y) ⟶ Z)
  (h₀ : stdSimplex.δ 1 ▷ (X ⊗ Y) ≫ h = snd _ _ ≫ fst X Y ≫ a)
  (h₁ : stdSimplex.δ 0 ▷ (X ⊗ Y) ≫ h = snd _ _ ≫ snd X Y ≫ b)

@[reassoc (attr := simp)]
theorem fatJoinInclLeft_fatJoinDesc : fatJoinInclLeft X Y ≫ fatJoinDesc a b h h₀ h₁ = a := by
  rw [fatJoinInclLeft, Category.assoc, fatJoinDesc, IsPushout.inl_desc, coprod.inl_desc]

@[reassoc (attr := simp)]
theorem fatJoinInclRight_fatJoinDesc : fatJoinInclRight X Y ≫ fatJoinDesc a b h h₀ h₁ = b := by
  rw [fatJoinInclRight, Category.assoc, fatJoinDesc, IsPushout.inl_desc, coprod.inr_desc]

@[reassoc (attr := simp)]
theorem fatJoinCyl_fatJoinDesc : fatJoinCyl X Y ≫ fatJoinDesc a b h h₀ h₁ = h :=
  IsPushout.inr_desc _ _ _ _

theorem eq_fatJoinDesc (g : fatJoin X Y ⟶ Z) (hl : fatJoinInclLeft X Y ≫ g = a)
    (hr : fatJoinInclRight X Y ≫ g = b) (hc : fatJoinCyl X Y ≫ g = h) :
    g = fatJoinDesc a b h h₀ h₁ :=
  fatJoin_hom_ext (by rw [hl, fatJoinInclLeft_fatJoinDesc])
    (by rw [hr, fatJoinInclRight_fatJoinDesc]) (by rw [hc, fatJoinCyl_fatJoinDesc])

end Desc

noncomputable def fatJoinMap {X' Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    fatJoin X Y ⟶ fatJoin X' Y' :=
  fatJoinDesc (f ≫ fatJoinInclLeft X' Y') (g ≫ fatJoinInclRight X' Y')
    (Δ[1] ◁ (f ⊗ₘ g) ≫ fatJoinCyl X' Y')
    (by rw [← whisker_exchange_assoc, stdSimplex_δ_one_whiskerRight_fatJoinCyl,
      whiskerLeft_snd_assoc, tensorHom_fst_assoc])
    (by rw [← whisker_exchange_assoc, stdSimplex_δ_zero_whiskerRight_fatJoinCyl,
      whiskerLeft_snd_assoc, tensorHom_snd_assoc])

section Map

variable {X' Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')

@[reassoc (attr := simp)]
theorem fatJoinInclLeft_fatJoinMap :
    fatJoinInclLeft X Y ≫ fatJoinMap f g = f ≫ fatJoinInclLeft X' Y' :=
  fatJoinInclLeft_fatJoinDesc _ _ _ _ _

@[reassoc (attr := simp)]
theorem fatJoinInclRight_fatJoinMap :
    fatJoinInclRight X Y ≫ fatJoinMap f g = g ≫ fatJoinInclRight X' Y' :=
  fatJoinInclRight_fatJoinDesc _ _ _ _ _

@[reassoc (attr := simp)]
theorem fatJoinCyl_fatJoinMap :
    fatJoinCyl X Y ≫ fatJoinMap f g = Δ[1] ◁ (f ⊗ₘ g) ≫ fatJoinCyl X' Y' :=
  fatJoinCyl_fatJoinDesc _ _ _ _ _

end Map

@[simp]
theorem fatJoinMap_id : fatJoinMap (𝟙 X) (𝟙 Y) = 𝟙 _ :=
  fatJoin_hom_ext (by simp) (by simp) (by simp)

@[reassoc]
theorem fatJoinMap_comp {X' Y' X'' Y'' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') (f' : X' ⟶ X'')
    (g' : Y' ⟶ Y'') : fatJoinMap (f ≫ f') (g ≫ g') = fatJoinMap f g ≫ fatJoinMap f' g' :=
  fatJoin_hom_ext (by simp) (by simp)
    (by rw [fatJoinCyl_fatJoinMap, fatJoinCyl_fatJoinMap_assoc, fatJoinCyl_fatJoinMap,
      ← whiskerLeft_comp_assoc, tensorHom_comp_tensorHom])

@[reassoc]
theorem fatJoinBoundaryMap_naturality {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    fatJoinBoundaryMap X Y ≫ coprod.map f g =
      (∂Δ[1] : SSet.{u}) ◁ (f ⊗ₘ g) ≫ fatJoinBoundaryMap X' Y' := by
  refine boundaryOneTensor_hom_ext ?_ ?_
  · rw [fatJoinBoundaryMap, fatJoinBoundaryMap,
      boundary_ι_one_whiskerRight_boundaryOneTensorDesc_assoc, ← whisker_exchange_assoc,
      boundary_ι_one_whiskerRight_boundaryOneTensorDesc, whiskerLeft_snd_assoc]
    simp only [Category.assoc, coprod.inl_map, tensorHom_fst_assoc]
  · rw [fatJoinBoundaryMap, fatJoinBoundaryMap,
      boundary_ι_zero_whiskerRight_boundaryOneTensorDesc_assoc, ← whisker_exchange_assoc,
      boundary_ι_zero_whiskerRight_boundaryOneTensorDesc, whiskerLeft_snd_assoc]
    simp only [Category.assoc, coprod.inr_map, tensorHom_snd_assoc]

private lemma mono_coprod_map {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') [Mono f]
    [Mono g] :
    Mono (coprod.map f g) := by
  rw [← coprod.desc_comp_inl_comp_inr]
  refine FunctorToTypes.mono_coprodDesc_of_disjoint _ _ fun U ↦ ?_
  have hc := (isColimitMapCoconeBinaryCofanEquiv ((evaluation _ _).obj U) _ _)
    (isColimitOfPreserves ((evaluation _ _).obj U) (coprodIsCoprod X' Y'))
  obtain ⟨-, -, hcompl⟩ := (Types.binaryCofan_isColimit_iff _).mp ⟨hc⟩
  refine hcompl.disjoint.mono ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨f.app U x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨g.app U x, rfl⟩

private lemma mono_tensorHom {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') [Mono f]
    [Mono g] :
    Mono (f ⊗ₘ g) :=
  ⟨fun a b h ↦ by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · refine (cancel_mono f).1 ?_
      simpa using congrArg (· ≫ fst _ _) h
    · refine (cancel_mono g).1 ?_
      simpa using congrArg (· ≫ snd _ _) h⟩

@[reassoc]
theorem fatJoinIncl_fatJoinMap {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    fatJoinIncl X Y ≫ fatJoinMap f g = coprod.map f g ≫ fatJoinIncl X' Y' := by
  refine coprod.hom_ext ?_ ?_
  · exact (fatJoinInclLeft_fatJoinMap f g).trans (coprod.inl_map_assoc _ _ _).symm
  · exact (fatJoinInclRight_fatJoinMap f g).trans (coprod.inr_map_assoc _ _ _).symm

instance mono_fatJoinMap {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') [Mono f] [Mono g] :
    Mono (fatJoinMap f g) := by
  have := mono_tensorHom f g
  have := mono_coprod_map f g
  have : Mono ((∂Δ[1]).ι ▷ (X' ⊗ Y')) := by
    rw [← tensorHom_id]
    exact mono_tensorHom _ _
  exact mono_of_isPushout_of_isPullback (isPushout_fatJoin X Y).flip
    (isPushout_fatJoin X' Y').flip (isPullback_whiskerRight_whiskerLeft (∂Δ[1]).ι (f ⊗ₘ g))
    (fatJoinBoundaryMap_naturality f g)
    (fatJoinCyl_fatJoinMap f g) (fatJoinIncl_fatJoinMap f g)

theorem isIso_fatJoinInclLeft_of_isInitial (X : SSet.{u}) {Y : SSet.{u}} (hY : IsInitial Y) :
    IsIso (fatJoinInclLeft X Y) := by
  have h : IsInitial (X ⊗ Y) := IsInitial.isInitialObj (tensorLeft X) _ hY
  have : IsIso ((∂Δ[1]).ι ▷ (X ⊗ Y)) :=
    isIso_of_isInitial (IsInitial.isInitialObj (tensorLeft _) _ h)
      (IsInitial.isInitialObj (tensorLeft _) _ h) _
  have := (isPushout_fatJoin X Y).isIso_inl_of_isIso
  have : IsIso (coprod.inl : X ⟶ X ⨿ Y) :=
    (IsPushout.of_hasBinaryCoproduct' X Y).isIso_inl_of_isIso
      (isIso_of_isInitial initialIsInitial hY _)
  rw [fatJoinInclLeft]
  infer_instance

theorem isIso_fatJoinInclRight_of_isInitial {X : SSet.{u}} (Y : SSet.{u}) (hX : IsInitial X) :
    IsIso (fatJoinInclRight X Y) := by
  have h : IsInitial (X ⊗ Y) := IsInitial.isInitialObj (tensorRight Y) _ hX
  have : IsIso ((∂Δ[1]).ι ▷ (X ⊗ Y)) :=
    isIso_of_isInitial (IsInitial.isInitialObj (tensorLeft _) _ h)
      (IsInitial.isInitialObj (tensorLeft _) _ h) _
  have := (isPushout_fatJoin X Y).isIso_inl_of_isIso
  have : IsIso (coprod.inr : Y ⟶ X ⨿ Y) :=
    (IsPushout.of_hasBinaryCoproduct' X Y).isIso_inr_of_isIso
      (isIso_of_isInitial initialIsInitial hX _)
  rw [fatJoinInclRight]
  infer_instance

theorem exists_fatJoinIncl_app_eq (X Y : SSet.{u}) (v : (fatJoin X Y) _⦋0⦌) :
    ∃ w, (fatJoinIncl X Y).app _ w = v := by
  obtain ⟨w, rfl⟩ | ⟨c, rfl⟩ := Types.eq_or_eq_of_isPushout ((isPushout_fatJoin X Y).app _) v
  · exact ⟨w, rfl⟩
  · have hc : c.1 ∈ (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).obj (op ⦋0⦌) := by
      rw [boundary_obj_eq_univ 0 1]
      trivial
    exact ⟨(fatJoinBoundaryMap X Y).app _ (⟨c.1, hc⟩, c.2),
      ConcreteCategory.congr_hom (congr_app (isPushout_fatJoin X Y).w (op ⦋0⦌)) _⟩

end FatJoin

section FatSlice

noncomputable def fatJoinRightUnder (T : SSet.{u}) : SSet.{u} ⥤ Under T where
  obj X := Under.mk (fatJoinInclRight X T)
  map f := Under.homMk (fatJoinMap f (𝟙 T)) (by simp)
  map_id X := by ext1; exact fatJoinMap_id
  map_comp f g := by
    ext1
    exact (congrArg₂ fatJoinMap rfl (Category.comp_id (𝟙 T)).symm).trans (fatJoinMap_comp _ _ _ _)

private noncomputable def swapIso (T D Y : SSet.{u}) : T ⊗ (D ⊗ Y) ≅ D ⊗ (Y ⊗ T) where
  hom := lift (snd _ _ ≫ fst _ _) (lift (snd _ _ ≫ snd _ _) (fst _ _))
  inv := lift (snd _ _ ≫ snd _ _) (lift (fst _ _) (snd _ _ ≫ fst _ _))

@[reassoc]
private lemma whiskerLeft_whiskerRight_swapIso_hom {T D D' : SSet.{u}} (Y : SSet.{u})
    (f : D ⟶ D') : T ◁ (f ▷ Y) ≫ (swapIso T D' Y).hom = (swapIso T D Y).hom ≫ f ▷ (Y ⊗ T) := by
  ext1
  · simp [swapIso]
  · ext1 <;> simp [swapIso, -whiskerRight_tensor]

@[reassoc]
private lemma whiskerLeft_whiskerLeft_swapIso_hom {T Y Y' : SSet.{u}} (D : SSet.{u})
    (f : Y ⟶ Y') : T ◁ (D ◁ f) ≫ (swapIso T D Y').hom = (swapIso T D Y).hom ≫ D ◁ (f ▷ T) := by
  ext1
  · simp [swapIso]
  · ext1 <;> simp [swapIso]

variable {T Z : SSet.{u}}

private lemma fatJoinEnds_iff {Y : SSet.{u}} (h : Δ[1] ⊗ (Y ⊗ T) ⟶ Z) (a : Y ⟶ Z) (t : T ⟶ Z) :
    (stdSimplex.δ 1 ▷ (Y ⊗ T) ≫ h = snd _ _ ≫ fst Y T ≫ a ∧
      stdSimplex.δ 0 ▷ (Y ⊗ T) ≫ h = snd _ _ ≫ snd Y T ≫ t) ↔
    (stdSimplex.δ 1 ▷ Y ≫ curry ((swapIso T Δ[1] Y).hom ≫ h) =
        snd _ _ ≫ a ≫ constDiagram T Z ∧
      stdSimplex.δ 0 ▷ Y ≫ curry ((swapIso T Δ[1] Y).hom ≫ h) =
        snd _ _ ≫ toUnit Y ≫ diagramPoint t) := by
  have e (f : Δ[0] ⟶ Δ[1]) (k : Δ[0] ⊗ (Y ⊗ T) ⟶ Z) (k' : T ⊗ (Δ[0] ⊗ Y) ⟶ Z)
      (hk : (swapIso T Δ[0] Y).hom ≫ k = k') :
      f ▷ (Y ⊗ T) ≫ h = k ↔ f ▷ Y ≫ curry ((swapIso T Δ[1] Y).hom ≫ h) = curry k' := by
    rw [← curry_natural_left, whiskerLeft_whiskerRight_swapIso_hom_assoc, ← hk,
      curry_injective.eq_iff, cancel_epi]
  rw [e _ _ (snd _ _ ≫ snd _ _ ≫ a) (by simp [swapIso]),
    e _ _ (fst _ _ ≫ t) (by simp [swapIso]), constDiagram, diagramPoint,
    ← curry_natural_left, ← curry_natural_left, ← curry_natural_left]
  simp only [← curry_natural_left, whiskerLeft_snd, whiskerLeft_snd_assoc, whiskerLeft_fst_assoc]

private lemma fatJoinUnderEnds {Y : SSet.{u}} {t : Under T} (φ : (fatJoinRightUnder T).obj Y ⟶ t) :
    stdSimplex.δ 1 ▷ (Y ⊗ T) ≫ fatJoinCyl Y T ≫ φ.right =
        snd _ _ ≫ fst Y T ≫ fatJoinInclLeft Y T ≫ φ.right ∧
      stdSimplex.δ 0 ▷ (Y ⊗ T) ≫ fatJoinCyl Y T ≫ φ.right = snd _ _ ≫ snd Y T ≫ t.hom :=
  ⟨stdSimplex_δ_one_whiskerRight_fatJoinCyl_assoc _ _ _,
    (stdSimplex_δ_zero_whiskerRight_fatJoinCyl_assoc _ _ _).trans
      (congrArg (snd _ _ ≫ snd Y T ≫ ·) (Under.w φ))⟩

private noncomputable def fatJoinUnderHomEquiv (Y : SSet.{u}) (t : Under T) :
    ((fatJoinRightUnder T).obj Y ⟶ t) ≃
      {q : (Y ⟶ t.right) × (Δ[1] ⊗ (Y ⊗ T) ⟶ t.right) //
        stdSimplex.δ 1 ▷ (Y ⊗ T) ≫ q.2 = snd _ _ ≫ fst Y T ≫ q.1 ∧
          stdSimplex.δ 0 ▷ (Y ⊗ T) ≫ q.2 = snd _ _ ≫ snd Y T ≫ t.hom} where
  toFun φ := ⟨(fatJoinInclLeft Y T ≫ φ.right, fatJoinCyl Y T ≫ φ.right), fatJoinUnderEnds φ⟩
  invFun q := Under.homMk (fatJoinDesc q.1.1 t.hom q.1.2 q.2.1 q.2.2)
    (fatJoinInclRight_fatJoinDesc _ _ _ _ _)
  left_inv φ := Under.UnderMorphism.ext (eq_fatJoinDesc (X := Y) (Y := T) _ _ _
    (fatJoinUnderEnds φ).1 (fatJoinUnderEnds φ).2 φ.right rfl (Under.w φ) rfl).symm
  right_inv q := Subtype.ext (Prod.ext (fatJoinInclLeft_fatJoinDesc _ _ _ q.2.1 q.2.2)
    (fatJoinCyl_fatJoinDesc _ _ _ q.2.1 q.2.2))

private noncomputable def fatJoinCurryEquiv (Y : SSet.{u}) (t : Under T) :
    {q : (Y ⟶ t.right) × (Δ[1] ⊗ (Y ⊗ T) ⟶ t.right) //
        stdSimplex.δ 1 ▷ (Y ⊗ T) ≫ q.2 = snd _ _ ≫ fst Y T ≫ q.1 ∧
          stdSimplex.δ 0 ▷ (Y ⊗ T) ≫ q.2 = snd _ _ ≫ snd Y T ≫ t.hom} ≃
      {p : (Y ⟶ t.right) × (Δ[1] ⊗ Y ⟶ (ihom T).obj t.right) //
        stdSimplex.δ 1 ▷ Y ≫ p.2 = snd _ _ ≫ p.1 ≫ constDiagram T t.right ∧
          stdSimplex.δ 0 ▷ Y ≫ p.2 = snd _ _ ≫ toUnit Y ≫ diagramPoint t.hom} where
  toFun q := ⟨(q.1.1, curry ((swapIso T Δ[1] Y).hom ≫ q.1.2)), (fatJoinEnds_iff _ _ _).1 q.2⟩
  invFun p := ⟨(p.1.1, (swapIso T Δ[1] Y).inv ≫ uncurry p.1.2), (fatJoinEnds_iff _ _ _).2 (by
    rw [Iso.hom_inv_id_assoc, curry_uncurry]
    exact p.2)⟩
  left_inv q := Subtype.ext (Prod.ext rfl (by
    dsimp only
    rw [uncurry_curry, Iso.inv_hom_id_assoc]))
  right_inv p := Subtype.ext (Prod.ext rfl (by
    dsimp only
    rw [Iso.hom_inv_id_assoc, curry_uncurry]))

private noncomputable def fatJoinHomEquiv (Y : SSet.{u}) (t : Under T) :
    ((fatJoinRightUnder T).obj Y ⟶ t) ≃ (Y ⟶ commaCone t.hom) :=
  (fatJoinUnderHomEquiv Y t).trans ((fatJoinCurryEquiv Y t).trans
    (commaConeHomEquiv t.hom Y).symm)

private lemma fatJoinHomEquiv_arrow (Y : SSet.{u}) (t : Under T)
    (φ : (fatJoinRightUnder T).obj Y ⟶ t) :
    fatJoinHomEquiv Y t φ ≫ commaConeArrow t.hom =
      curry (curry ((swapIso T Δ[1] Y).hom ≫ fatJoinCyl Y T ≫ φ.right)) := by
  rw [fatJoinHomEquiv, Equiv.trans_apply, Equiv.trans_apply, commaConeHomEquiv_symm_apply_arrow]
  simp [fatJoinCurryEquiv, fatJoinUnderHomEquiv]

private lemma fatJoinHomEquiv_π (Y : SSet.{u}) (t : Under T)
    (φ : (fatJoinRightUnder T).obj Y ⟶ t) :
    fatJoinHomEquiv Y t φ ≫ commaConeπ t.hom = fatJoinInclLeft Y T ≫ φ.right := by
  rw [fatJoinHomEquiv, Equiv.trans_apply, Equiv.trans_apply, commaConeHomEquiv_symm_apply_π]
  simp [fatJoinCurryEquiv, fatJoinUnderHomEquiv]

private lemma fatJoinHomEquiv_naturality (Y' Y : SSet.{u}) (t : Under T) (f : Y' ⟶ Y)
    (g : (fatJoinRightUnder T).obj Y ⟶ t) :
    fatJoinHomEquiv Y' t ((fatJoinRightUnder T).map f ≫ g) = f ≫ fatJoinHomEquiv Y t g := by
  refine (isPullback_commaCone t.hom).hom_ext ?_ ?_
  · rw [fatJoinHomEquiv_arrow, Category.assoc, fatJoinHomEquiv_arrow, Under.comp_right]
    refine (congrArg (fun k ↦ curry (curry ((swapIso T Δ[1] Y').hom ≫ k)))
      (fatJoinCyl_fatJoinMap_assoc f (𝟙 T) g.right)).trans ?_
    rw [tensorHom_id, ← whiskerLeft_whiskerLeft_swapIso_hom_assoc, curry_natural_left,
      curry_natural_left]
  · rw [fatJoinHomEquiv_π, Category.assoc, fatJoinHomEquiv_π, Under.comp_right]
    exact fatJoinInclLeft_fatJoinMap_assoc f (𝟙 T) g.right

private noncomputable def commaConeUnder (T : SSet.{u}) : Under T ⥤ SSet.{u} :=
  Adjunction.rightAdjointOfEquiv (G_obj := fun t ↦ commaCone t.hom) fatJoinHomEquiv
    fatJoinHomEquiv_naturality

private noncomputable def fatJoinRightUnderCommaConeAdjunction (T : SSet.{u}) :
    fatJoinRightUnder T ⊣ commaConeUnder T :=
  Adjunction.adjunctionOfEquivRight _ _

instance preservesColimitsOfSize_fatJoinRightUnder (T : SSet.{u}) :
    PreservesColimitsOfSize.{u, u} (fatJoinRightUnder T) :=
  (fatJoinRightUnderCommaConeAdjunction T).leftAdjoint_preservesColimits

noncomputable def fatSlice (T : SSet.{u}) : Under T ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} (uliftYoneda.{u} ⋙ fatJoinRightUnder T)

noncomputable def fatJoinRightUnderAdjunction (T : SSet.{u}) :
    fatJoinRightUnder T ⊣ fatSlice T :=
  have : PreservesColimitsOfSize.{0, u} (fatJoinRightUnder T) := preservesColimitsOfSize_shrink _
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1}
    (fatJoinRightUnder T) (Iso.refl _)
  Presheaf.uliftYonedaAdjunction.{0} (fatJoinRightUnder T) (Iso.refl _).hom

noncomputable def fatSliceObjEquiv (T : SSet.{u}) (t : Under T) (n : ℕ) :
    ((fatSlice T).obj t).obj (op ⦋n⦌) ≃
      {f : fatJoin Δ[n] T ⟶ t.right // fatJoinInclRight Δ[n] T ≫ f = t.hom} :=
  Equiv.ulift.trans
    { toFun f := ⟨f.right, Under.w f⟩
      invFun f := Under.homMk f.1 f.2
      left_inv _ := rfl
      right_inv _ := rfl }

noncomputable def commaConeIsoFatSlice {K X : SSet.{u}} (d : K ⟶ X) :
    commaCone d ≅ (fatSlice K).obj (Under.mk d) :=
  ((fatJoinRightUnderCommaConeAdjunction K).rightAdjointUniq
    (fatJoinRightUnderAdjunction K)).app (Under.mk d)

theorem commaConeIsoFatSlice_inv_commaConeπ {K X Y : SSet.{u}} (d : K ⟶ X)
    (g : Y ⟶ (fatSlice K).obj (Under.mk d)) :
    g ≫ (commaConeIsoFatSlice d).inv ≫ commaConeπ d =
      fatJoinInclLeft Y K ≫ (((fatJoinRightUnderAdjunction K).homEquiv _ _).symm g).right := by
  have hU : (fatJoinRightUnderCommaConeAdjunction K).homEquiv Y (Under.mk d)
      (((fatJoinRightUnderAdjunction K).homEquiv _ _).symm g) =
        g ≫ (Adjunction.rightAdjointUniq (fatJoinRightUnderAdjunction K)
          (fatJoinRightUnderCommaConeAdjunction K)).hom.app (Under.mk d) := by
    apply ((fatJoinRightUnderCommaConeAdjunction K).homEquiv Y (Under.mk d)).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_symm_rightAdjointUniq_hom_app, Adjunction.homEquiv_counit]
  have hπ := congrArg (fun k : Y ⟶ commaCone d ↦ k ≫ commaConeπ d) hU
  have he : (fatJoinRightUnderCommaConeAdjunction K).homEquiv Y (Under.mk d) =
      fatJoinHomEquiv Y (Under.mk d) :=
    congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) Y) (Under.mk d)
  have hφ := congrArg (fun k : Y ⟶ commaCone d ↦ k ≫ commaConeπ d)
    (congrFun (congrArg DFunLike.coe he) (((fatJoinRightUnderAdjunction K).homEquiv _ _).symm g))
  exact ((Category.assoc _ _ _).symm.trans hπ.symm).trans
    (hφ.trans (fatJoinHomEquiv_π Y (Under.mk d) _))

end FatSlice

section LeftUnder

private noncomputable def fatJoinSpanRight (X : SSet.{u}) :
    SSet.{u} ⥤ WalkingSpan ⥤ SSet.{u} where
  obj Y := span (fatJoinBoundaryMap X Y) ((∂Δ[1]).ι ▷ (X ⊗ Y))
  map g := spanHomMk ((∂Δ[1] : SSet.{u}) ◁ (X ◁ g)) (coprod.map (𝟙 X) g) (Δ[1] ◁ (X ◁ g))
    (by
      rw [span_map_fst, span_map_fst, ← id_tensorHom]
      exact fatJoinBoundaryMap_naturality (𝟙 X) g)
    (by rw [span_map_snd, span_map_snd]; exact (whisker_exchange _ _).symm)
  map_id _ := by ext (_ | _ | _) : 2 <;> dsimp [spanHomMk] <;> simp
  map_comp _ _ := by ext (_ | _ | _) : 2 <;> dsimp [spanHomMk] <;> simp

noncomputable def fatJoinLeftUnder (X : SSet.{u}) : SSet.{u} ⥤ Under X where
  obj Y := Under.mk (fatJoinInclLeft X Y)
  map g := Under.homMk (fatJoinMap (𝟙 X) g) (by simp)
  map_id Y := by ext1; exact fatJoinMap_id
  map_comp f g := by
    ext1
    exact (congrArg₂ fatJoinMap (Category.comp_id (𝟙 X)).symm rfl).trans (fatJoinMap_comp _ _ _ _)

private lemma colimMap_fatJoinSpanRight_map (X : SSet.{u}) {Y Y' : SSet.{u}} (g : Y ⟶ Y') :
    (colimMap ((fatJoinSpanRight X).map g) : fatJoin X Y ⟶ fatJoin X Y') = fatJoinMap (𝟙 X) g := by
  refine fatJoin_hom_ext ?_ ?_ ?_
  · refine Eq.trans ?_ (fatJoinInclLeft_fatJoinMap (𝟙 X) g).symm
    exact (Category.assoc _ _ _).trans ((congrArg (coprod.inl ≫ ·) (ι_colimMap _ _)).trans
      (coprod.inl_map_assoc _ _ _))
  · refine Eq.trans ?_ (fatJoinInclRight_fatJoinMap (𝟙 X) g).symm
    exact (Category.assoc _ _ _).trans ((congrArg (coprod.inr ≫ ·) (ι_colimMap _ _)).trans
      (coprod.inr_map_assoc _ _ _))
  · refine Eq.trans ?_ (fatJoinCyl_fatJoinMap (𝟙 X) g).symm
    rw [id_tensorHom]
    exact ι_colimMap _ _

private noncomputable def fatJoinSpanRightCompColimIso (X : SSet.{u}) :
    fatJoinSpanRight X ⋙ colim ≅ fatJoinLeftUnder X ⋙ Under.forget X :=
  NatIso.ofComponents (fun Y ↦ Iso.refl (fatJoin X Y)) fun g ↦
    (Category.comp_id _).trans ((colimMap_fatJoinSpanRight_map X g).trans (Category.id_comp _).symm)

private instance preservesColimitsOfShape_fatJoinSpanRight (X : SSet.{u}) (K : Type*)
    [Category* K] [IsConnected K] : PreservesColimitsOfShape K (fatJoinSpanRight X) := by
  refine preservesColimitsOfShape_of_evaluation _ _ fun k ↦ ?_
  rcases k with _ | _ | _
  · exact preservesColimitsOfShape_of_natIso (F := tensorLeft X ⋙ tensorLeft (∂Δ[1] : SSet.{u}))
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
        (Category.comp_id _).trans (Category.id_comp _).symm)
  · exact preservesColimitsOfShape_of_natIso (F := Under.costar X ⋙ Under.forget X)
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
        (Category.comp_id _).trans (Category.id_comp _).symm)
  · exact preservesColimitsOfShape_of_natIso (F := tensorLeft X ⋙ tensorLeft Δ[1])
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
        (Category.comp_id _).trans (Category.id_comp _).symm)

instance preservesColimitsOfShape_fatJoinLeftUnder_comp_forget (X : SSet.{u}) (K : Type*)
    [Category* K] [IsConnected K] :
    PreservesColimitsOfShape K (fatJoinLeftUnder X ⋙ Under.forget X) :=
  preservesColimitsOfShape_of_natIso (fatJoinSpanRightCompColimIso X)

instance preservesColimitsOfSize_fatJoinLeftUnder (X : SSet.{u}) :
    PreservesColimitsOfSize.{u, u} (fatJoinLeftUnder X) where
  preservesColimitsOfShape {J} _ :=
    have : IsIso ((fatJoinLeftUnder X).obj (⊥_ SSet.{u})).hom :=
      isIso_fatJoinInclLeft_of_isInitial X initialIsInitial
    WithInitial.preservesColimitsOfShape_of_isIso_hom.{0, u} initialIsInitial _
      (fun _ _ _ ↦ inferInstance) J

end LeftUnder

section ToJoin

private lemma stdSimplex_δ_one_comp_stdSimplexJoinIso_inv :
    stdSimplex.δ 1 ≫ (stdSimplexJoinIso.{u} 0 0).inv = joinInclLeft Δ[0] Δ[0] := by
  rw [Iso.comp_inv_eq, joinInclLeft_comp_stdSimplexJoinIso_hom]
  refine congrArg stdSimplex.map ?_
  ext i : 3
  fin_cases i
  rfl

private lemma stdSimplex_δ_zero_comp_stdSimplexJoinIso_inv :
    stdSimplex.δ 0 ≫ (stdSimplexJoinIso.{u} 0 0).inv = joinInclRight Δ[0] Δ[0] := by
  rw [Iso.comp_inv_eq, joinInclRight_comp_stdSimplexJoinIso_hom]
  refine congrArg stdSimplex.map ?_
  ext i : 3
  fin_cases i
  rfl

variable (X Y : SSet.{u})

noncomputable def fatJoinCylToJoin : Δ[1] ⊗ (X ⊗ Y) ⟶ join X Y :=
  (β_ _ _).hom ≫ (X ⊗ Y) ◁ (stdSimplexJoinIso 0 0).inv ≫ tensorJoinTensorMap (X ⊗ Y) Δ[0] Δ[0] ≫
    joinMap (fst _ _ ≫ fst X Y) (fst _ _ ≫ snd X Y)

@[reassoc]
theorem stdSimplex_δ_one_whiskerRight_fatJoinCylToJoin :
    stdSimplex.δ 1 ▷ (X ⊗ Y) ≫ fatJoinCylToJoin X Y = snd _ _ ≫ fst X Y ≫ joinInclLeft X Y := by
  rw [fatJoinCylToJoin, BraidedCategory.braiding_naturality_left_assoc, ← whiskerLeft_comp_assoc,
    stdSimplex_δ_one_comp_stdSimplexJoinIso_inv,
    whiskerLeft_joinInclLeft_comp_tensorJoinTensorMap_assoc, joinInclLeft_comp_joinMap]
  simp only [Category.assoc, braiding_hom_fst_assoc]

@[reassoc]
theorem stdSimplex_δ_zero_whiskerRight_fatJoinCylToJoin :
    stdSimplex.δ 0 ▷ (X ⊗ Y) ≫ fatJoinCylToJoin X Y = snd _ _ ≫ snd X Y ≫ joinInclRight X Y := by
  rw [fatJoinCylToJoin, BraidedCategory.braiding_naturality_left_assoc, ← whiskerLeft_comp_assoc,
    stdSimplex_δ_zero_comp_stdSimplexJoinIso_inv,
    whiskerLeft_joinInclRight_comp_tensorJoinTensorMap_assoc, joinInclRight_comp_joinMap]
  simp only [Category.assoc, braiding_hom_fst_assoc]

noncomputable def fatJoinToJoin : fatJoin X Y ⟶ join X Y :=
  fatJoinDesc (joinInclLeft X Y) (joinInclRight X Y) (fatJoinCylToJoin X Y)
    (stdSimplex_δ_one_whiskerRight_fatJoinCylToJoin X Y)
    (stdSimplex_δ_zero_whiskerRight_fatJoinCylToJoin X Y)

@[reassoc (attr := simp)]
theorem fatJoinInclLeft_fatJoinToJoin :
    fatJoinInclLeft X Y ≫ fatJoinToJoin X Y = joinInclLeft X Y :=
  fatJoinInclLeft_fatJoinDesc _ _ _ _ _

@[reassoc (attr := simp)]
theorem fatJoinInclRight_fatJoinToJoin :
    fatJoinInclRight X Y ≫ fatJoinToJoin X Y = joinInclRight X Y :=
  fatJoinInclRight_fatJoinDesc _ _ _ _ _

@[reassoc (attr := simp)]
theorem fatJoinCyl_fatJoinToJoin : fatJoinCyl X Y ≫ fatJoinToJoin X Y = fatJoinCylToJoin X Y :=
  fatJoinCyl_fatJoinDesc _ _ _ _ _

variable {X Y}

@[reassoc]
theorem whiskerLeft_tensorHom_fatJoinCylToJoin {X' Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    Δ[1] ◁ (f ⊗ₘ g) ≫ fatJoinCylToJoin X' Y' = fatJoinCylToJoin X Y ≫ joinMap f g := by
  rw [fatJoinCylToJoin, fatJoinCylToJoin, BraidedCategory.braiding_naturality_right_assoc,
    ← whisker_exchange_assoc, whiskerRight_comp_tensorJoinTensorMap_assoc, joinMap_comp_joinMap]
  simp only [Category.assoc, joinMap_comp_joinMap, whiskerRight_fst_assoc, tensorHom_fst,
    tensorHom_snd]

@[reassoc]
theorem fatJoinMap_comp_fatJoinToJoin {X' Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    fatJoinMap f g ≫ fatJoinToJoin X' Y' = fatJoinToJoin X Y ≫ joinMap f g :=
  fatJoin_hom_ext (by simp [joinInclLeft_comp_joinMap]) (by simp [joinInclRight_comp_joinMap])
    (by simp [whiskerLeft_tensorHom_fatJoinCylToJoin])

@[simps]
noncomputable def fatJoinToJoinUnder (T : SSet.{u}) : fatJoinRightUnder T ⟶ joinRightUnder T where
  app X := Under.homMk (fatJoinToJoin X T) (fatJoinInclRight_fatJoinToJoin X T)
  naturality _ _ f := Under.UnderMorphism.ext (fatJoinMap_comp_fatJoinToJoin f (𝟙 _))

noncomputable def sliceToFatSlice (T : SSet.{u}) : slice T ⟶ fatSlice T :=
  conjugateEquiv (joinRightUnderAdjunction T) (fatJoinRightUnderAdjunction T)
    (fatJoinToJoinUnder T)

private lemma stdSimplex_hom_ext_of_const {M N : ℕ} {f g : Δ[M] ⟶ (Δ[N] : SSet.{u})}
    (h : ∀ i, stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋M⦌ i) ≫ f =
      stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋M⦌ i) ≫ g) : f = g := by
  obtain ⟨f, rfl⟩ := stdSimplex.map_surjective f
  obtain ⟨g, rfl⟩ := stdSimplex.map_surjective g
  refine congrArg _ (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ ?_)))
  have h' := h i
  simp only [← stdSimplex.map_comp] at h'
  exact congrArg (fun φ : ⦋0⦌ ⟶ ⦋N⦌ ↦ φ.toOrderHom 0) (stdSimplex.map_injective h')

private lemma const_zero_eq_δ_one :
    SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 = SimplexCategory.δ 1 := by
  ext i : 3
  fin_cases i
  rfl

private lemma const_one_eq_δ_zero :
    SimplexCategory.const ⦋0⦌ ⦋1⦌ 1 = SimplexCategory.δ 0 := by
  ext i : 3
  fin_cases i
  rfl

@[reassoc]
theorem lift_const_zero_fatJoinCylToJoin {X Y : SSet.{u}} (a : Δ[0] ⟶ X) (b : Δ[0] ⟶ Y) :
    lift (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)) (lift a b) ≫ fatJoinCylToJoin X Y =
      a ≫ joinInclLeft X Y := by
  rw [const_zero_eq_δ_one, ← Category.id_comp (stdSimplex.map _), ← lift_whiskerRight,
    Category.assoc]
  exact (congrArg (lift (𝟙 _) (lift a b) ≫ ·)
    (stdSimplex_δ_one_whiskerRight_fatJoinCylToJoin X Y)).trans (by simp)

@[reassoc]
theorem lift_const_one_fatJoinCylToJoin {X Y : SSet.{u}} (a : Δ[0] ⟶ X) (b : Δ[0] ⟶ Y) :
    lift (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)) (lift a b) ≫ fatJoinCylToJoin X Y =
      b ≫ joinInclRight X Y := by
  rw [const_one_eq_δ_zero, ← Category.id_comp (stdSimplex.map _), ← lift_whiskerRight,
    Category.assoc]
  exact (congrArg (lift (𝟙 _) (lift a b) ≫ ·)
    (stdSimplex_δ_zero_whiskerRight_fatJoinCylToJoin X Y)).trans (by simp)

section Section

variable (m n : ℕ)

private def sectionInterval : ⦋m + n + 1⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.mkHom ⟨fun i ↦ if (i : ℕ) ≤ m then 0 else 1, fun i j h ↦ by
    have : (i : ℕ) ≤ j := h
    beta_reduce
    split_ifs <;> first | exact le_rfl | exact Fin.zero_le _ | omega⟩

private def sectionLeft : ⦋m + n + 1⦌ ⟶ ⦋m⦌ :=
  SimplexCategory.mkHom ⟨fun i ↦ ⟨min i m, by omega⟩, fun i j h ↦ by
    have : (i : ℕ) ≤ j := h
    exact Fin.mk_le_mk.2 (by omega)⟩

private def sectionRight : ⦋m + n + 1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom ⟨fun i ↦ ⟨i - (m + 1), by omega⟩, fun i j h ↦ by
    have : (i : ℕ) ≤ j := h
    exact Fin.mk_le_mk.2 (by omega)⟩

noncomputable def fatJoinStdSimplexSection : Δ[m + n + 1] ⟶ fatJoin Δ[m] Δ[n] :=
  lift (stdSimplex.map (sectionInterval m n))
    (lift (stdSimplex.map (sectionLeft m n)) (stdSimplex.map (sectionRight m n))) ≫
      fatJoinCyl Δ[m] Δ[n]

theorem fatJoinStdSimplexSection_fatJoinToJoin :
    fatJoinStdSimplexSection m n ≫ fatJoinToJoin Δ[m] Δ[n] = (stdSimplexJoinIso m n).inv := by
  rw [← Iso.comp_hom_eq_id]
  refine stdSimplex_hom_ext_of_const fun i ↦ ?_
  rw [Category.comp_id, fatJoinStdSimplexSection, Category.assoc, Category.assoc,
    fatJoinCyl_fatJoinToJoin_assoc, comp_lift_assoc, comp_lift, ← stdSimplex.map_comp,
    ← stdSimplex.map_comp, ← stdSimplex.map_comp]
  by_cases hi : (i : ℕ) ≤ m
  · have hu : SimplexCategory.const ⦋0⦌ ⦋m + n + 1⦌ i ≫ sectionInterval m n =
        SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 := by
      ext j : 3
      exact if_pos hi
    rw [hu, ← Category.assoc]
    refine (congrArg (· ≫ (stdSimplexJoinIso m n).hom)
      (lift_const_zero_fatJoinCylToJoin (X := Δ[m]) (Y := Δ[n]) _ _)).trans ?_
    rw [Category.assoc, joinInclLeft_comp_stdSimplexJoinIso_hom,
      ← stdSimplex.map_comp]
    refine congrArg _ ?_
    ext j : 3
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      AugmentedSimplexCategory.inl'_eval, sectionLeft, SimplexCategory.const_apply]
    refine Fin.ext ?_
    simp only [Fin.val_cast, Fin.val_castAdd, SimplexCategory.mkHom,
      SimplexCategory.Hom.toOrderHom_mk]
    dsimp only [DFunLike.coe]
    omega
  · have hu : SimplexCategory.const ⦋0⦌ ⦋m + n + 1⦌ i ≫ sectionInterval m n =
        SimplexCategory.const ⦋0⦌ ⦋1⦌ 1 := by
      ext j : 3
      exact if_neg hi
    rw [hu, ← Category.assoc]
    refine (congrArg (· ≫ (stdSimplexJoinIso m n).hom)
      (lift_const_one_fatJoinCylToJoin (X := Δ[m]) (Y := Δ[n]) _ _)).trans ?_
    rw [Category.assoc, joinInclRight_comp_stdSimplexJoinIso_hom,
      ← stdSimplex.map_comp]
    refine congrArg _ ?_
    ext j : 3
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      AugmentedSimplexCategory.inr'_eval, sectionRight, SimplexCategory.const_apply]
    refine Fin.ext ?_
    simp only [Fin.val_cast, Fin.val_natAdd, SimplexCategory.mkHom,
      SimplexCategory.Hom.toOrderHom_mk]
    dsimp only [DFunLike.coe]
    omega

end Section

end ToJoin

section Homotopies

private abbrev vtx {k : ℕ} (i : Fin (k + 1)) : (Δ[0] : SSet.{u}) ⟶ Δ[k] :=
  stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i)

private def prodStdSimplexHom {a b c : ℕ} (f : Fin (a + 1) × Fin (b + 1) →o Fin (c + 1)) :
    (Δ[a] ⊗ Δ[b] : SSet.{u}) ⟶ Δ[c] where
  app _ := ↾fun z ↦ stdSimplex.objMk
    (f.comp ((stdSimplex.asOrderHom z.1).prod (stdSimplex.asOrderHom z.2)))
  naturality _ _ _ := rfl

@[reassoc]
private lemma vtx_comp_map {k l : ℕ} (i : Fin (k + 1)) (φ : ⦋k⦌ ⟶ ⦋l⦌) :
    vtx.{u} i ≫ stdSimplex.map φ = vtx (φ.toOrderHom i) := by
  rw [← stdSimplex.map_comp]
  rfl

@[reassoc]
private lemma lift_vtx_prodStdSimplexHom {a b c : ℕ}
    (f : Fin (a + 1) × Fin (b + 1) →o Fin (c + 1)) (i : Fin (a + 1)) (j : Fin (b + 1)) :
    lift (vtx.{u} i) (vtx j) ≫ prodStdSimplexHom f = vtx (f (i, j)) := by
  apply yonedaEquiv.injective
  ext x
  fin_cases x
  rfl

private lemma eq_vtx {k : ℕ} (v : (Δ[0] : SSet.{u}) ⟶ Δ[k]) : ∃ i, v = vtx i := by
  obtain ⟨φ, rfl⟩ := stdSimplex.map_surjective v
  refine ⟨φ.toOrderHom 0, congrArg _ ?_⟩
  ext x : 3
  fin_cases x
  rfl

private lemma hom_ext_vtx {A : SSet.{u}} {N : ℕ} {f g : A ⟶ Δ[N]}
    (h : ∀ v : Δ[0] ⟶ A, v ≫ f = v ≫ g) : f = g := by
  ext ⟨k⟩ a
  induction k using SimplexCategory.rec with | _ d => ?_
  refine stdSimplex.ext _ _ fun i ↦ ?_
  have := congr_arg (fun φ ↦ (yonedaEquiv φ : (Δ[N] : SSet.{u}) _⦋0⦌) 0)
    (h (yonedaEquiv.symm (A.map (SimplexCategory.const ⦋0⦌ ⦋d⦌ i).op a)))
  simp only [yonedaEquiv_symm_comp, Equiv.apply_symm_apply] at this
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply] at this
  exact this

private lemma hom_ext_vtx₃ {a b c N : ℕ} {f g : (Δ[a] ⊗ (Δ[b] ⊗ Δ[c]) : SSet.{u}) ⟶ Δ[N]}
    (h : ∀ i j k, lift (vtx i) (lift (vtx j) (vtx k)) ≫ f =
      lift (vtx i) (lift (vtx j) (vtx k)) ≫ g) : f = g := hom_ext_vtx fun v ↦ by
  obtain ⟨i, hi⟩ := eq_vtx (v ≫ fst _ _)
  obtain ⟨j, hj⟩ := eq_vtx (v ≫ snd _ _ ≫ fst _ _)
  obtain ⟨k, hk⟩ := eq_vtx (v ≫ snd _ _ ≫ snd _ _)
  obtain rfl : v = lift (vtx i) (lift (vtx j) (vtx k)) := by
    refine CartesianMonoidalCategory.hom_ext _ _ (by simpa using hi) ?_
    exact CartesianMonoidalCategory.hom_ext _ _ (by simpa using hj) (by simpa using hk)
  exact h i j k

private lemma hom_ext_vtx₄ {a b c d N : ℕ}
    {f g : (Δ[a] ⊗ (Δ[b] ⊗ (Δ[c] ⊗ Δ[d])) : SSet.{u}) ⟶ Δ[N]}
    (h : ∀ i j k l, lift (vtx i) (lift (vtx j) (lift (vtx k) (vtx l))) ≫ f =
      lift (vtx i) (lift (vtx j) (lift (vtx k) (vtx l))) ≫ g) : f = g := hom_ext_vtx fun v ↦ by
  obtain ⟨i, hi⟩ := eq_vtx (v ≫ fst _ _)
  obtain ⟨j, hj⟩ := eq_vtx (v ≫ snd _ _ ≫ fst _ _)
  obtain ⟨k, hk⟩ := eq_vtx (v ≫ snd _ _ ≫ snd _ _ ≫ fst _ _)
  obtain ⟨l, hl⟩ := eq_vtx (v ≫ snd _ _ ≫ snd _ _ ≫ snd _ _)
  obtain rfl : v = lift (vtx i) (lift (vtx j) (lift (vtx k) (vtx l))) := by
    refine CartesianMonoidalCategory.hom_ext _ _ (by simpa using hi) ?_
    refine CartesianMonoidalCategory.hom_ext _ _ (by simpa using hj) ?_
    exact CartesianMonoidalCategory.hom_ext _ _ (by simpa using hk) (by simpa using hl)
  exact h i j k l

private lemma hom_ext₃ {A X Y Z : SSet.{u}} {f g : A ⟶ X ⊗ (Y ⊗ Z)}
    (h₁ : f ≫ fst _ _ = g ≫ fst _ _)
    (h₂ : f ≫ snd _ _ ≫ fst _ _ = g ≫ snd _ _ ≫ fst _ _)
    (h₃ : f ≫ snd _ _ ≫ snd _ _ = g ≫ snd _ _ ≫ snd _ _) : f = g :=
  CartesianMonoidalCategory.hom_ext _ _ h₁ (CartesianMonoidalCategory.hom_ext _ _ h₂ h₃)

variable (m n : ℕ)

private def mulHom : Fin 2 × Fin (n + 1) →o Fin (n + 1) :=
  ⟨fun p ↦ if p.1 = 0 then 0 else p.2, fun p q h ↦ by
    obtain ⟨h₁, h₂⟩ := h
    dsimp only
    split_ifs with hp hq hq
    · exact le_rfl
    · exact Fin.zero_le _
    · exact absurd (le_antisymm (hq ▸ h₁) (Fin.zero_le _)) hp
    · exact h₂⟩

private def topHom : Fin 2 × Fin (m + 1) →o Fin (m + 1) :=
  ⟨fun p ↦ if p.1 = 0 then p.2 else Fin.last m, fun p q h ↦ by
    obtain ⟨h₁, h₂⟩ := h
    dsimp only
    split_ifs with hp hq hq
    · exact h₂
    · exact Fin.le_last _
    · exact absurd (le_antisymm (hq ▸ h₁) (Fin.zero_le _)) hp
    · exact le_rfl⟩

private def maxHom : Fin 2 × Fin 2 →o Fin 2 :=
  ⟨fun p ↦ max p.1 p.2, fun _ _ h ↦ max_le_max h.1 h.2⟩

private def minHom : Fin 2 × Fin 2 →o Fin 2 :=
  ⟨fun p ↦ min p.1 p.2, fun _ _ h ↦ min_le_min h.1 h.2⟩

private noncomputable def prismH :
    (Δ[1] ⊗ (Δ[1] ⊗ (Δ[m] ⊗ Δ[n])) : SSet.{u}) ⟶ Δ[1] ⊗ (Δ[m] ⊗ Δ[n]) :=
  lift (snd _ _ ≫ fst _ _) (lift (snd _ _ ≫ snd _ _ ≫ fst _ _)
    (lift (lift (fst _ _) (snd _ _ ≫ fst _ _) ≫ prodStdSimplexHom maxHom)
      (snd _ _ ≫ snd _ _ ≫ snd _ _) ≫ prodStdSimplexHom (mulHom n)))

private noncomputable def prismK :
    (Δ[1] ⊗ (Δ[1] ⊗ (Δ[m] ⊗ Δ[n])) : SSet.{u}) ⟶ Δ[1] ⊗ (Δ[m] ⊗ Δ[n]) :=
  lift (snd _ _ ≫ fst _ _)
    (lift (lift (lift (fst _ _) (snd _ _ ≫ fst _ _) ≫ prodStdSimplexHom minHom)
      (snd _ _ ≫ snd _ _ ≫ fst _ _) ≫ prodStdSimplexHom (topHom m))
    (lift (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _ ≫ snd _ _) ≫ prodStdSimplexHom (mulHom n)))

private lemma const_eq_vtx {k : ℕ} (i : Fin (k + 1)) :
    (SSet.const (stdSimplex.obj₀Equiv.symm i) : (Δ[0] : SSet.{u}) ⟶ Δ[k]) = vtx i := by
  apply yonedaEquiv.injective
  ext x
  fin_cases x
  rfl

@[reassoc]
private lemma vtx_comp_const {A : SSet.{u}} {k : ℕ} (v : Δ[0] ⟶ A) (i : Fin (k + 1)) :
    v ≫ SSet.const (stdSimplex.obj₀Equiv.symm i) = vtx i := by
  rw [comp_const]
  exact const_eq_vtx i

@[reassoc]
private lemma vtx_comp_δ {k : ℕ} (i : Fin (k + 1)) (j : Fin (k + 2)) :
    vtx.{u} i ≫ stdSimplex.δ j = vtx ((SimplexCategory.δ j).toOrderHom i) :=
  vtx_comp_map i _

@[reassoc]
private lemma lift_vtx_zero_fatJoinCylToJoin {X Y : SSet.{u}} (a : Δ[0] ⟶ X) (b : Δ[0] ⟶ Y) :
    lift (vtx (k := 1) 0) (lift a b) ≫ fatJoinCylToJoin X Y = a ≫ joinInclLeft X Y :=
  lift_const_zero_fatJoinCylToJoin a b

@[reassoc]
private lemma lift_vtx_one_fatJoinCylToJoin {X Y : SSet.{u}} (a : Δ[0] ⟶ X) (b : Δ[0] ⟶ Y) :
    lift (vtx (k := 1) 1) (lift a b) ≫ fatJoinCylToJoin X Y = b ≫ joinInclRight X Y :=
  lift_const_one_fatJoinCylToJoin a b

section Homotopy

variable {X Y : SSet.{u}} (H : Δ[1] ⊗ (Δ[1] ⊗ (X ⊗ Y)) ⟶ Δ[1] ⊗ (X ⊗ Y))
  (G₀ G₁ : Δ[1] ⊗ (Δ[0] ⊗ (X ⊗ Y)) ⟶ Δ[0] ⊗ (X ⊗ Y))
  (h₀ : Δ[1] ◁ (stdSimplex.δ 1 ▷ (X ⊗ Y)) ≫ H = G₀ ≫ stdSimplex.δ 1 ▷ (X ⊗ Y))
  (h₁ : Δ[1] ◁ (stdSimplex.δ 0 ▷ (X ⊗ Y)) ≫ H = G₁ ≫ stdSimplex.δ 0 ▷ (X ⊗ Y))
  (h₀' : G₀ ≫ snd _ _ ≫ fst X Y = snd _ _ ≫ snd _ _ ≫ fst X Y)
  (h₁' : G₁ ≫ snd _ _ ≫ snd X Y = snd _ _ ≫ snd _ _ ≫ snd X Y)

private noncomputable def prismCurry : fatJoin X Y ⟶ (ihom Δ[1]).obj (fatJoin X Y) :=
  fatJoinDesc (curry (snd _ _ ≫ fatJoinInclLeft X Y)) (curry (snd _ _ ≫ fatJoinInclRight X Y))
    (curry (H ≫ fatJoinCyl X Y))
    (by
      rw [← curry_natural_left, ← curry_natural_left, reassoc_of% h₀,
        stdSimplex_δ_one_whiskerRight_fatJoinCyl, reassoc_of% h₀', whiskerLeft_snd_assoc,
        ← curry_natural_left, whiskerLeft_snd_assoc])
    (by
      rw [← curry_natural_left, ← curry_natural_left, reassoc_of% h₁,
        stdSimplex_δ_zero_whiskerRight_fatJoinCyl, reassoc_of% h₁', whiskerLeft_snd_assoc,
        ← curry_natural_left, whiskerLeft_snd_assoc])

include h₀ h₁ h₀' h₁' in
private lemma fatJoinIncl_prismCurry :
    fatJoinIncl X Y ≫ prismCurry H G₀ G₁ h₀ h₁ h₀' h₁' = curry (snd _ _ ≫ fatJoinIncl X Y) := by
  refine coprod.hom_ext ?_ ?_
  · rw [← Category.assoc]
    exact (fatJoinInclLeft_fatJoinDesc _ _ _ _ _).trans (by
      rw [← curry_natural_left, whiskerLeft_snd_assoc]
      rfl)
  · rw [← Category.assoc]
    exact (fatJoinInclRight_fatJoinDesc _ _ _ _ _).trans (by
      rw [← curry_natural_left, whiskerLeft_snd_assoc]
      rfl)

include h₀ h₁ h₀' h₁' in
private lemma whiskerLeft_fatJoinIncl_uncurry_prismCurry :
    Δ[1] ◁ fatJoinIncl X Y ≫ uncurry (prismCurry H G₀ G₁ h₀ h₁ h₀' h₁') =
      snd _ _ ≫ fatJoinIncl X Y := by
  rw [← uncurry_natural_left, fatJoinIncl_prismCurry, uncurry_curry]

private lemma lift_uncurry {A B Z : SSet.{u}} (c : A ⟶ Δ[1]) (f : A ⟶ B)
    (g : B ⟶ (ihom Δ[1]).obj Z) : lift c f ≫ uncurry g = lift c (𝟙 A) ≫ uncurry (f ≫ g) := by
  rw [uncurry_natural_left, ← Category.assoc, lift_whiskerLeft, Category.id_comp]

include h₀ h₁ h₀' h₁' in
private lemma fatJoinInclLeft_lift_const_uncurry_prismCurry (x : (Δ[1] : SSet.{u}) _⦋0⦌) :
    fatJoinInclLeft X Y ≫ lift (SSet.const x) (𝟙 _) ≫
      uncurry (prismCurry H G₀ G₁ h₀ h₁ h₀' h₁') = fatJoinInclLeft X Y := by
  rw [comp_lift_assoc, comp_const, Category.comp_id, lift_uncurry, prismCurry,
    fatJoinInclLeft_fatJoinDesc, uncurry_curry, lift_snd_assoc, Category.id_comp]

include h₀ h₁ h₀' h₁' in
private lemma fatJoinInclRight_lift_const_uncurry_prismCurry (x : (Δ[1] : SSet.{u}) _⦋0⦌) :
    fatJoinInclRight X Y ≫ lift (SSet.const x) (𝟙 _) ≫
      uncurry (prismCurry H G₀ G₁ h₀ h₁ h₀' h₁') = fatJoinInclRight X Y := by
  rw [comp_lift_assoc, comp_const, Category.comp_id, lift_uncurry, prismCurry,
    fatJoinInclRight_fatJoinDesc, uncurry_curry, lift_snd_assoc, Category.id_comp]

include h₀ h₁ h₀' h₁' in
private lemma fatJoinCyl_lift_const_uncurry_prismCurry (x : (Δ[1] : SSet.{u}) _⦋0⦌) :
    fatJoinCyl X Y ≫ lift (SSet.const x) (𝟙 _) ≫
      uncurry (prismCurry H G₀ G₁ h₀ h₁ h₀' h₁') =
        lift (SSet.const x) (𝟙 _) ≫ H ≫ fatJoinCyl X Y := by
  rw [comp_lift_assoc, comp_const, Category.comp_id, lift_uncurry, prismCurry,
    fatJoinCyl_fatJoinDesc, uncurry_curry]

end Homotopy

variable (m n : ℕ)

private lemma prismH_δ_one :
    Δ[1] ◁ (stdSimplex.δ 1 ▷ (Δ[m] ⊗ Δ[n])) ≫ prismH.{u} m n =
      lift (snd _ _ ≫ fst _ _) (lift (snd _ _ ≫ snd _ _ ≫ fst _ _)
        (lift (fst _ _) (snd _ _ ≫ snd _ _ ≫ snd _ _) ≫ prodStdSimplexHom (mulHom n))) ≫
        stdSimplex.δ 1 ▷ (Δ[m] ⊗ Δ[n]) := by
  refine hom_ext₃ ?_ ?_ ?_ <;> refine hom_ext_vtx₄ fun i j k l ↦ ?_ <;>
    (simp only [prismH, comp_lift_assoc, comp_lift, lift_fst, lift_snd, lift_fst_assoc,
      lift_snd_assoc, Category.assoc, whiskerLeft_fst, whiskerLeft_snd_assoc,
      whiskerRight_snd_assoc, whiskerRight_fst,
      vtx_comp_δ, lift_vtx_prodStdSimplexHom]
     try (refine congrArg vtx ?_; fin_cases i <;> fin_cases j <;> rfl))

private lemma prismH_δ_zero :
    Δ[1] ◁ (stdSimplex.δ 0 ▷ (Δ[m] ⊗ Δ[n])) ≫ prismH.{u} m n =
      snd _ _ ≫ stdSimplex.δ 0 ▷ (Δ[m] ⊗ Δ[n]) := by
  refine hom_ext₃ ?_ ?_ ?_ <;> refine hom_ext_vtx₄ fun i j k l ↦ ?_ <;>
    (simp only [prismH, comp_lift_assoc, comp_lift, lift_fst, lift_snd, lift_fst_assoc,
      lift_snd_assoc, Category.assoc, whiskerLeft_fst,
      whiskerLeft_snd_assoc, whiskerRight_snd_assoc,
      whiskerRight_fst, vtx_comp_δ,
      lift_vtx_prodStdSimplexHom]
     try (refine congrArg vtx ?_; fin_cases i <;> fin_cases j <;> rfl))

private lemma prismK_δ_one :
    Δ[1] ◁ (stdSimplex.δ 1 ▷ (Δ[m] ⊗ Δ[n])) ≫ prismK.{u} m n =
      lift (snd _ _ ≫ fst _ _) (lift (snd _ _ ≫ snd _ _ ≫ fst _ _)
        (snd _ _ ≫ fst _ _ ≫ vtx 0)) ≫ stdSimplex.δ 1 ▷ (Δ[m] ⊗ Δ[n]) := by
  refine hom_ext₃ ?_ ?_ ?_ <;> refine hom_ext_vtx₄ fun i j k l ↦ ?_ <;>
    (simp only [prismK, comp_lift_assoc, comp_lift, lift_fst, lift_snd, lift_fst_assoc,
      lift_snd_assoc, Category.assoc, whiskerLeft_fst,
      whiskerLeft_snd_assoc, whiskerRight_snd_assoc,
      whiskerRight_fst, vtx_comp_δ, vtx_comp_map,
      lift_vtx_prodStdSimplexHom]
     try (refine congrArg vtx ?_; fin_cases i <;> fin_cases j <;> rfl))

private lemma prismK_δ_zero :
    Δ[1] ◁ (stdSimplex.δ 0 ▷ (Δ[m] ⊗ Δ[n])) ≫ prismK.{u} m n =
      lift (snd _ _ ≫ fst _ _) (lift (lift (fst _ _) (snd _ _ ≫ snd _ _ ≫ fst _ _) ≫
        prodStdSimplexHom (topHom m)) (snd _ _ ≫ snd _ _ ≫ snd _ _)) ≫
        stdSimplex.δ 0 ▷ (Δ[m] ⊗ Δ[n]) := by
  refine hom_ext₃ ?_ ?_ ?_ <;> refine hom_ext_vtx₄ fun i j k l ↦ ?_ <;>
    (simp only [prismK, comp_lift_assoc, comp_lift, lift_fst, lift_snd, lift_fst_assoc,
      lift_snd_assoc, Category.assoc, whiskerLeft_fst,
      whiskerLeft_snd_assoc, whiskerRight_snd_assoc,
      whiskerRight_fst, vtx_comp_δ,
      lift_vtx_prodStdSimplexHom]
     try (refine congrArg vtx ?_; fin_cases i <;> fin_cases j <;> rfl))

noncomputable def fatJoinStdSimplexHomotopyId : Δ[1] ⊗ fatJoin Δ[m] Δ[n] ⟶ fatJoin Δ[m] Δ[n] :=
  uncurry (prismCurry (prismH.{u} m n) _ (snd _ _) (prismH_δ_one m n) (prismH_δ_zero m n)
    (by simp) (by simp))

noncomputable def fatJoinStdSimplexHomotopySection :
    Δ[1] ⊗ fatJoin Δ[m] Δ[n] ⟶ fatJoin Δ[m] Δ[n] :=
  uncurry (prismCurry (prismK.{u} m n) _ _ (prismK_δ_one m n) (prismK_δ_zero m n)
    (by simp) (by simp))

theorem whiskerLeft_fatJoinIncl_fatJoinStdSimplexHomotopyId :
    Δ[1] ◁ fatJoinIncl Δ[m] Δ[n] ≫ fatJoinStdSimplexHomotopyId.{u} m n =
      snd _ _ ≫ fatJoinIncl Δ[m] Δ[n] :=
  whiskerLeft_fatJoinIncl_uncurry_prismCurry _ _ _ _ _ _ _

theorem whiskerLeft_fatJoinIncl_fatJoinStdSimplexHomotopySection :
    Δ[1] ◁ fatJoinIncl Δ[m] Δ[n] ≫ fatJoinStdSimplexHomotopySection.{u} m n =
      snd _ _ ≫ fatJoinIncl Δ[m] Δ[n] :=
  whiskerLeft_fatJoinIncl_uncurry_prismCurry _ _ _ _ _ _ _

theorem fatJoinStdSimplexHomotopyId_one :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm 1)) (𝟙 _) ≫
      fatJoinStdSimplexHomotopyId.{u} m n = 𝟙 _ := by
  refine fatJoin_hom_ext ((fatJoinInclLeft_lift_const_uncurry_prismCurry _ _ _ _ _ _ _ _).trans
    (Category.comp_id _).symm)
    ((fatJoinInclRight_lift_const_uncurry_prismCurry _ _ _ _ _ _ _ _).trans
    (Category.comp_id _).symm) ((fatJoinCyl_lift_const_uncurry_prismCurry _ _ _ _ _ _ _ _).trans ?_)
  rw [Category.comp_id, ← Category.assoc]
  refine (congrArg (· ≫ fatJoinCyl _ _) ?_).trans (Category.id_comp _)
  refine (hom_ext₃ ?_ ?_ ?_ : lift (SSet.const (stdSimplex.obj₀Equiv.symm 1)) (𝟙 _) ≫
    prismH.{u} m n = _) <;> refine hom_ext_vtx₃ fun i j k ↦ ?_ <;>
    (simp only [prismH, comp_lift_assoc, comp_lift, lift_fst, lift_snd,
      lift_snd_assoc, Category.id_comp, vtx_comp_const, lift_vtx_prodStdSimplexHom]
     try (refine congrArg vtx ?_; fin_cases i <;> rfl))

theorem fatJoinStdSimplexHomotopySection_zero :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 _) ≫
      fatJoinStdSimplexHomotopySection.{u} m n =
    lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 _) ≫
      fatJoinStdSimplexHomotopyId.{u} m n := by
  have e : lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 _) ≫ prismK.{u} m n =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 _) ≫ prismH.{u} m n := by
    refine hom_ext₃ ?_ ?_ ?_ <;> refine hom_ext_vtx₃ fun i j k ↦ ?_ <;>
      (simp only [prismH, prismK, comp_lift_assoc, comp_lift, lift_fst, lift_snd,
      lift_snd_assoc, Category.id_comp, vtx_comp_const, lift_vtx_prodStdSimplexHom]
       try (refine congrArg vtx ?_; fin_cases i <;> rfl))
  refine fatJoin_hom_ext ((fatJoinInclLeft_lift_const_uncurry_prismCurry _ _ _ _ _ _ _ _).trans
    (fatJoinInclLeft_lift_const_uncurry_prismCurry _ _ _ _ _ _ _ _).symm)
    ((fatJoinInclRight_lift_const_uncurry_prismCurry _ _ _ _ _ _ _ _).trans
    (fatJoinInclRight_lift_const_uncurry_prismCurry _ _ _ _ _ _ _ _).symm)
    ((fatJoinCyl_lift_const_uncurry_prismCurry _ _ _ _ _ _ _ _).trans ?_)
  exact ((reassoc_of% e) (fatJoinCyl Δ[m] Δ[n])).trans
    (fatJoinCyl_lift_const_uncurry_prismCurry _ _ _ _ _ _ _ _).symm

private lemma prismK_one_vtx (i : Fin (1 + 1)) (j : Fin (m + 1)) (k : Fin (n + 1)) :
    lift (vtx i) (lift (vtx j) (vtx k)) ≫
      lift (SSet.const (stdSimplex.obj₀Equiv.symm 1)) (𝟙 _) ≫ prismK.{u} m n =
    lift (vtx i) (lift (vtx j) (vtx k)) ≫ fatJoinCylToJoin Δ[m] Δ[n] ≫
      (stdSimplexJoinIso m n).hom ≫ lift (stdSimplex.map (sectionInterval m n))
        (lift (stdSimplex.map (sectionLeft m n)) (stdSimplex.map (sectionRight m n))) := by
  have two : ∀ x : Fin (1 + 1), x = 0 ∨ x = 1 := by decide
  rcases two i with rfl | rfl
  · rw [lift_vtx_zero_fatJoinCylToJoin_assoc,
      reassoc_of% (joinInclLeft_comp_stdSimplexJoinIso_hom m n)]
    refine hom_ext₃ ?_ ?_ ?_ <;>
      simp only [prismK, mulHom, topHom, minHom,
        ] <;>
      simp only [comp_lift_assoc, comp_lift, lift_fst, lift_snd, lift_snd_assoc,
          Category.id_comp, vtx_comp_const, vtx_comp_map,
          vtx_comp_map_assoc,
          lift_vtx_prodStdSimplexHom] <;>
        (refine congrArg vtx (Fin.ext ?_)) <;>
        simp only [AugmentedSimplexCategory.inl'_eval,
          sectionInterval, sectionLeft, sectionRight, SimplexCategory.mkHom,
          SimplexCategory.Hom.toOrderHom_mk] <;>
        dsimp only [DFunLike.coe] <;>
        simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_zero] <;>
        (try split_ifs with hh) <;> (try simp only [Fin.val_zero, Fin.val_last]) <;>
        first | rfl | omega | exact absurd hh (by decide)
  · rw [lift_vtx_one_fatJoinCylToJoin_assoc,
      reassoc_of% (joinInclRight_comp_stdSimplexJoinIso_hom m n)]
    refine hom_ext₃ ?_ ?_ ?_ <;>
      simp only [prismK, mulHom, topHom, minHom,
        ] <;>
      simp only [comp_lift_assoc, comp_lift, lift_fst, lift_snd, lift_snd_assoc,
          Category.id_comp, vtx_comp_const, vtx_comp_map,
          vtx_comp_map_assoc,
          lift_vtx_prodStdSimplexHom] <;>
        (refine congrArg vtx (Fin.ext ?_)) <;>
        simp only [AugmentedSimplexCategory.inr'_eval,
          sectionInterval, sectionLeft, sectionRight, SimplexCategory.mkHom,
          SimplexCategory.Hom.toOrderHom_mk] <;>
        dsimp only [DFunLike.coe] <;>
        simp only [Fin.val_cast, Fin.val_natAdd] <;>
        (try split_ifs with hh) <;> (try simp only [Fin.val_zero, Fin.val_last]) <;>
        first | rfl | omega | exact absurd hh (by decide)

theorem fatJoinStdSimplexHomotopySection_one :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm 1)) (𝟙 _) ≫
      fatJoinStdSimplexHomotopySection.{u} m n =
    fatJoinToJoin Δ[m] Δ[n] ≫ (stdSimplexJoinIso m n).hom ≫ fatJoinStdSimplexSection m n := by
  refine fatJoin_hom_ext ((fatJoinInclLeft_lift_const_uncurry_prismCurry _ _ _ _ _ _ _ _).trans
    ?_) ((fatJoinInclRight_lift_const_uncurry_prismCurry _ _ _ _ _ _ _ _).trans ?_)
    ((fatJoinCyl_lift_const_uncurry_prismCurry _ _ _ _ _ _ _ _).trans ?_)
  · rw [fatJoinInclLeft_fatJoinToJoin_assoc,
      reassoc_of% (joinInclLeft_comp_stdSimplexJoinIso_hom m n), fatJoinStdSimplexSection]
    have e : stdSimplex.map (AugmentedSimplexCategory.inl' ⦋m⦌ ⦋n⦌) ≫
        lift (stdSimplex.map (sectionInterval m n))
          (lift (stdSimplex.map (sectionLeft m n)) (stdSimplex.map (sectionRight m n))) =
        lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (lift (𝟙 _)
          (SSet.const (stdSimplex.obj₀Equiv.symm 0))) ≫ stdSimplex.δ 1 ▷ (Δ[m] ⊗ Δ[n]) := by
      refine hom_ext₃ ?_ ?_ ?_ <;> refine hom_ext_vtx fun v ↦ ?_ <;>
        obtain ⟨i, rfl⟩ := eq_vtx v <;>
        simp only [comp_lift, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc,
          Category.assoc, vtx_comp_const, vtx_comp_const_assoc, vtx_comp_map, vtx_comp_map_assoc,
          whiskerRight_snd_assoc, whiskerRight_fst,
          vtx_comp_δ] <;>
        (refine congrArg vtx (Fin.ext ?_)) <;>
        simp only [AugmentedSimplexCategory.inl'_eval, sectionInterval, sectionLeft, sectionRight,
          SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
          ] <;>
        dsimp only [DFunLike.coe] <;>
        simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_zero] <;>
        (try split_ifs with hh) <;> (try simp only [Fin.val_zero]) <;>
        first | rfl | omega
    rw [reassoc_of% e, stdSimplex_δ_one_whiskerRight_fatJoinCyl, lift_snd_assoc, lift_fst_assoc,
      Category.id_comp]
  · rw [fatJoinInclRight_fatJoinToJoin_assoc,
      reassoc_of% (joinInclRight_comp_stdSimplexJoinIso_hom m n), fatJoinStdSimplexSection]
    have e : stdSimplex.map (AugmentedSimplexCategory.inr' ⦋m⦌ ⦋n⦌) ≫
        lift (stdSimplex.map (sectionInterval m n))
          (lift (stdSimplex.map (sectionLeft m n)) (stdSimplex.map (sectionRight m n))) =
        lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (lift
          (SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last m))) (𝟙 _)) ≫
            stdSimplex.δ 0 ▷ (Δ[m] ⊗ Δ[n]) := by
      refine hom_ext₃ ?_ ?_ ?_ <;> refine hom_ext_vtx fun v ↦ ?_ <;>
        obtain ⟨i, rfl⟩ := eq_vtx v <;>
        simp only [comp_lift, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc,
          Category.assoc, vtx_comp_const, vtx_comp_const_assoc, vtx_comp_map,
          vtx_comp_map_assoc, whiskerRight_snd_assoc, whiskerRight_fst,
          vtx_comp_δ] <;>
        (refine congrArg vtx (Fin.ext ?_)) <;>
        simp only [AugmentedSimplexCategory.inr'_eval,
          sectionInterval, sectionLeft, sectionRight, SimplexCategory.mkHom,
          SimplexCategory.Hom.toOrderHom_mk] <;>
        dsimp only [DFunLike.coe] <;>
        simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_last] <;>
        (try split_ifs with hh) <;> (try simp only [Fin.val_zero]) <;>
        first | rfl | omega
    rw [reassoc_of% e, stdSimplex_δ_zero_whiskerRight_fatJoinCyl, lift_snd_assoc, lift_snd_assoc,
      Category.id_comp]
  · rw [fatJoinCyl_fatJoinToJoin_assoc, fatJoinStdSimplexSection]
    have key : lift (SSet.const (stdSimplex.obj₀Equiv.symm 1)) (𝟙 _) ≫ prismK.{u} m n =
        fatJoinCylToJoin Δ[m] Δ[n] ≫ (stdSimplexJoinIso m n).hom ≫
          lift (stdSimplex.map (sectionInterval m n))
            (lift (stdSimplex.map (sectionLeft m n)) (stdSimplex.map (sectionRight m n))) := by
      refine hom_ext₃ ?_ ?_ ?_ <;> refine hom_ext_vtx₃ fun i j k ↦ ?_ <;>
        simpa only [Category.assoc] using congrArg (· ≫ _) (prismK_one_vtx m n i j k)
    exact (reassoc_of% key) _

end Homotopies

end SSet
