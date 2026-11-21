import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.MappingSpaceMap

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory Simplicial

universe u

namespace SSet

variable {A B A' B' : SSet.{u}}

noncomputable def commaObjectBase (α : Bool) (F : A ⟶ B) (b : 𝟙_ SSet.{u} ⟶ B) :
    A ⟶ (ihom (∂Δ[1] : SSet.{u})).obj B :=
  curry (boundaryOneTensorDesc (cond α F (toUnit A ≫ b)) (cond α (toUnit A ≫ b) F))

@[reassoc]
theorem commaObjectBase_comp_evalVertex_one (α : Bool) (F : A ⟶ B) (b : 𝟙_ SSet.{u} ⟶ B) :
    commaObjectBase α F b ≫
        evalVertex (yonedaEquiv (boundary.ι 1 : Δ[0] ⟶ (∂Δ[1] : SSet.{u}))) B =
      cond α F (toUnit A ≫ b) := by
  rw [commaObjectBase, comp_evalVertex, uncurry_curry, Equiv.symm_apply_apply,
    ← lift_whiskerRight, Category.assoc, boundary_ι_one_whiskerRight_boundaryOneTensorDesc,
    lift_snd_assoc, Category.id_comp]

@[reassoc]
theorem commaObjectBase_comp_evalVertex_zero (α : Bool) (F : A ⟶ B) (b : 𝟙_ SSet.{u} ⟶ B) :
    commaObjectBase α F b ≫
        evalVertex (yonedaEquiv (boundary.ι 0 : Δ[0] ⟶ (∂Δ[1] : SSet.{u}))) B =
      cond α (toUnit A ≫ b) F := by
  rw [commaObjectBase, comp_evalVertex, uncurry_curry, Equiv.symm_apply_apply,
    ← lift_whiskerRight, Category.assoc, boundary_ι_zero_whiskerRight_boundaryOneTensorDesc,
    lift_snd_assoc, Category.id_comp]

noncomputable def commaObject (α : Bool) (F : A ⟶ B) (b : 𝟙_ SSet.{u} ⟶ B) : SSet.{u} :=
  pullback ((pre (∂Δ[1]).ι).app B) (commaObjectBase α F b)

noncomputable def commaObjectπ (α : Bool) (F : A ⟶ B) (b : 𝟙_ SSet.{u} ⟶ B) :
    commaObject α F b ⟶ A :=
  pullback.snd ((pre (∂Δ[1]).ι).app B) (commaObjectBase α F b)

noncomputable def commaObjectArrow (α : Bool) (F : A ⟶ B) (b : 𝟙_ SSet.{u} ⟶ B) :
    commaObject α F b ⟶ (ihom Δ[1]).obj B :=
  pullback.fst ((pre (∂Δ[1]).ι).app B) (commaObjectBase α F b)

theorem isPullback_commaObject (α : Bool) (F : A ⟶ B) (b : 𝟙_ SSet.{u} ⟶ B) :
    IsPullback (commaObjectArrow α F b) (commaObjectπ α F b) ((pre (∂Δ[1]).ι).app B)
      (commaObjectBase α F b) :=
  IsPullback.of_hasPullback _ _

instance quasicategory_commaObject (α : Bool) (F : A ⟶ B) (b : 𝟙_ SSet.{u} ⟶ B)
    [A.Quasicategory] [B.Quasicategory] : (commaObject α F b).Quasicategory :=
  have := isofibration_pre_boundaryOne B
  have : InnerFibration (commaObjectπ α F b) := ⟨MorphismProperty.of_isPullback
    (P := innerFibrations) (isPullback_commaObject α F b) (mem_innerFibrations _)⟩
  quasicategory_of_innerFibration (commaObjectπ α F b)

theorem isofibration_commaObjectπ (α : Bool) (F : A ⟶ B) (b : 𝟙_ SSet.{u} ⟶ B)
    [A.Quasicategory] [B.Quasicategory] : Isofibration (commaObjectπ α F b) :=
  have := isofibration_pre_boundaryOne B
  isofibration_of_isPullback (isPullback_commaObject α F b)

section Functoriality

variable {F : A ⟶ B} {F' : A' ⟶ B'} {b : 𝟙_ SSet.{u} ⟶ B} {b' : 𝟙_ SSet.{u} ⟶ B'}

@[reassoc]
theorem commaObjectBase_comp_ihom_map (α : Bool) (u : A ⟶ A') (v : B ⟶ B')
    (hF : F ≫ v = u ≫ F') (hb : b ≫ v = b') :
    commaObjectBase α F b ≫ (ihom (∂Δ[1] : SSet.{u})).map v = u ≫ commaObjectBase α F' b' := by
  have h (β : Bool) : cond β F (toUnit A ≫ b) ≫ v = u ≫ cond β F' (toUnit A' ≫ b') := by
    cases β
    · rw [cond_false, cond_false, Category.assoc, hb, comp_toUnit_assoc]
    · exact hF
  rw [commaObjectBase, commaObjectBase, ← curry_natural_right, ← curry_natural_left]
  congr 1
  refine boundaryOneTensor_hom_ext ?_ ?_
  · rw [boundary_ι_one_whiskerRight_boundaryOneTensorDesc_assoc, ← whisker_exchange_assoc,
      boundary_ι_one_whiskerRight_boundaryOneTensorDesc, whiskerLeft_snd_assoc, h α]
  · have h' := h (!α)
    rw [Bool.cond_not, Bool.cond_not] at h'
    rw [boundary_ι_zero_whiskerRight_boundaryOneTensorDesc_assoc, ← whisker_exchange_assoc,
      boundary_ι_zero_whiskerRight_boundaryOneTensorDesc, whiskerLeft_snd_assoc, h']

noncomputable def commaObjectMap (α : Bool) (u : A ⟶ A') (v : B ⟶ B') (hF : F ≫ v = u ≫ F')
    (hb : b ≫ v = b') : commaObject α F b ⟶ commaObject α F' b' :=
  (isPullback_commaObject α F' b').lift (commaObjectArrow α F b ≫ (ihom Δ[1]).map v)
    (commaObjectπ α F b ≫ u) (by
      rw [Category.assoc, ← pre_comm_ihom_map, (isPullback_commaObject α F b).w_assoc,
        commaObjectBase_comp_ihom_map α u v hF hb, Category.assoc])

@[reassoc (attr := simp)]
theorem commaObjectMap_π (α : Bool) (u : A ⟶ A') (v : B ⟶ B') (hF : F ≫ v = u ≫ F')
    (hb : b ≫ v = b') :
    commaObjectMap α u v hF hb ≫ commaObjectπ α F' b' = commaObjectπ α F b ≫ u :=
  (isPullback_commaObject α F' b').lift_snd _ _ _

@[reassoc (attr := simp)]
theorem commaObjectMap_arrow (α : Bool) (u : A ⟶ A') (v : B ⟶ B') (hF : F ≫ v = u ≫ F')
    (hb : b ≫ v = b') :
    commaObjectMap α u v hF hb ≫ commaObjectArrow α F' b' =
      commaObjectArrow α F b ≫ (ihom Δ[1]).map v :=
  (isPullback_commaObject α F' b').lift_fst _ _ _

end Functoriality

end SSet
