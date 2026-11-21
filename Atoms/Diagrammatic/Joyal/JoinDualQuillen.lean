import Atoms.Diagrammatic.Joyal.JoinQuillen
import Atoms.Diagrammatic.Localization.Dual
import Atoms.Diagrammatic.JoinDual

open CategoryTheory CategoryTheory.WithInitial Limits Opposite MorphismProperty
  HomotopicalAlgebra Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open scoped DiagSet.Join

private noncomputable def dualJoinMapIdArrowIso (T : DiagSet.{u}) {A B : DiagSet.{u}}
    (g : A ⟶ B) :
    CategoryTheory.Arrow.mk ((DiagSet.dual Nat.bodd).map (joinMap (𝟙 T) g)) ≅
      CategoryTheory.Arrow.mk
        (joinMap ((DiagSet.dual Nat.bodd).map g) (𝟙 ((DiagSet.dual Nat.bodd).obj T))) :=
  CategoryTheory.Arrow.isoMk (joinDualIso T A) (joinDualIso T B)
    ((dual_map_joinMap_comp_joinDualIso_hom (𝟙 T) g).trans
      (by rw [CategoryTheory.Functor.map_id]; rfl)).symm

theorem trivialCofibration_toInfty_id_joinMap (T : DiagSet.{u}) {A B : DiagSet.{u}} {g : A ⟶ B}
    (hg : trivialCofibrations (DiagSet.Infty.{u} 1) ((DiagSet.toInfty 1).map g)) :
    trivialCofibrations (DiagSet.Infty.{u} 1) ((DiagSet.toInfty 1).map (joinMap (𝟙 T) g)) := by
  rw [← trivialCofibration_toInfty_dual_map_iff 1 Nat.bodd]
  exact ((trivialCofibrations (DiagSet.Infty.{u} 1)).arrow_mk_iso_iff
    (dualJoinMapIdArrowIso T g)).2 (trivialCofibration_toInfty_joinMap_id
      ((trivialCofibration_toInfty_dual_map_iff 1 Nat.bodd g).2 hg) _)

noncomputable def joinLeftUnderInfty (T : DiagSet.{u}) :
    DiagSet.Infty.{u} 1 ⥤ Under ((DiagSet.toInfty 1).obj T) :=
  WithInitial.joinLeftUnder T

noncomputable def cosliceInfty (T : DiagSet.{u}) :
    Under ((DiagSet.toInfty 1).obj T) ⥤ DiagSet.Infty.{u} 1 :=
  WithInitial.coslice T

noncomputable def joinLeftUnderAdjunctionInfty (T : DiagSet.{u}) :
    joinLeftUnderInfty T ⊣ cosliceInfty T :=
  WithInitial.joinLeftUnderAdjunction T

theorem isQuillen_joinLeftUnder (T : DiagSet.{u}) :
    (joinLeftUnderAdjunctionInfty T).IsQuillen where
  cofibrations_le _ _ g hg := (cofibration_iff _).1 ((cofibrations_under_iff _ _).2
    ((cofibration_iff _).2 (@mono_joinMap _ _ _ _ (𝟙 T) g _ hg)))
  trivialCofibrations_le _ _ _ hg := trivialCofibration_toInfty_id_joinMap T hg

theorem trivialCofibration_toInfty_pushoutObjObj_ι_of_trivialCofibration_right
    {S T A B : DiagSet.{u}} (j : S ⟶ T) [Mono j] {g : A ⟶ B}
    (hg : trivialCofibrations (DiagSet.Infty.{u} 1) ((DiagSet.toInfty 1).map g)) :
    trivialCofibrations (DiagSet.Infty.{u} 1)
      ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥 j g).ι) := by
  have : Mono g := ((mem_trivialCofibrations_iff _).1 hg).1.mem
  have hinl : trivialCofibrations (DiagSet.Infty.{u} 1)
      ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥 j g).inl) :=
    (trivialCofibrations (DiagSet.Infty.{u} 1)).of_isPushout
    (Functor.PushoutObjObj.ofHasPushout 𝒥 j g).isPushout
    (trivialCofibration_toInfty_id_joinMap S hg)
  have := ((mem_trivialCofibrations_iff _).1 hinl).2
  have : WeakEquivalence ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥 j g).inl ≫
      (DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥 j g).ι) := by
    rw [← Functor.map_comp, (Functor.PushoutObjObj.ofHasPushout 𝒥 j g).inl_ι]
    exact ((mem_trivialCofibrations_iff _).1 (trivialCofibration_toInfty_id_joinMap T hg)).2
  refine (mem_trivialCofibrations_iff _).2 ⟨(cofibration_iff _).2 ?_,
    weakEquivalence_of_precomp_of_fac (f := (DiagSet.toInfty 1).map
      (Functor.PushoutObjObj.ofHasPushout 𝒥 j g).inl) rfl⟩
  exact mono_pushoutObjObj_ι_join j g

theorem trivialCofibration_toInfty_pushoutObjObj_ι_of_anodyne_of_mono_right
    {S T A B : DiagSet.{u}} (j : S ⟶ T) [Mono j] {g : A ⟶ B}
    (hg : reversibleCylinder.{u}.anodyne (inftyGenerators 1) g) :
    trivialCofibrations (DiagSet.Infty.{u} 1)
      ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥 j g).ι) :=
  trivialCofibration_toInfty_pushoutObjObj_ι_of_trivialCofibration_right j
    (trivialCofibration_toInfty_of_anodyne hg)

theorem trivialCofibration_toInfty_pushoutObjObj_ι_of_anodyneGenerators_right (V : Atom)
    ⦃A B : DiagSet.{u}⦄ (g : A ⟶ B)
    (hg : reversibleCylinder.{u}.anodyneGenerators (inftyGenerators 1) g) :
    trivialCofibrations (DiagSet.Infty.{u} 1)
      ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (WithInitial.joinFunctor (C := Atom) : DiagSet × DiagSet ⥤ DiagSet))
        (sphereInclusion.{u} V) g).ι) := by
  refine trivialCofibration_toInfty_pushoutObjObj_ι_of_anodyne_of_mono_right (sphereInclusion V) ?_
  rw [reversibleCylinder.{u}.anodyne_eq_saturation_anodyneGenerators _
    (inftyGenerators_le_monomorphisms.{u} 1)]
  exact le_saturation _ _ hg

theorem fibration_leibnizCoslice {S T X Y : DiagSet.{u}} (j : S ⟶ T) [Mono j] {p : X ⟶ Y}
    [hp : Fibration ((DiagSet.toInfty 1).map p)] (t : T ⟶ X) :
    Fibration ((DiagSet.toInfty 1).map (WithInitial.leibnizCoslice j p t)) := by
  rw [fibration_iff, ← trivialCofibrations_rlp]
  intro K L i hi
  refine (hasLiftingProperty_leibnizCoslice_iff (Functor.PushoutObjObj.ofHasPushout 𝒥 j i) p t).2
    fun {a b} hsq _ => ?_
  exact ((hp.mem : reversibleCylinder.{u}.fibrations (inftyGenerators 1) p) _
    (trivialCofibration_toInfty_pushoutObjObj_ι_of_trivialCofibration_right j (g := i)
      hi)).sq_hasLift hsq

theorem isFibrant_coslice_of_isFibrant {T X : DiagSet.{u}}
    [hX : IsFibrant ((DiagSet.toInfty 1).obj X)] (t : T ⟶ X) :
    IsFibrant ((DiagSet.toInfty 1).obj ((WithInitial.coslice T).obj (Under.mk t))) :=
  have : IsFibrant (Under.mk t : Under ((DiagSet.toInfty 1).obj T)) :=
    (isFibrant_under_iff _ _).2 hX
  (isQuillen_joinLeftUnder T).isFibrant_obj (Under.mk t : Under ((DiagSet.toInfty 1).obj T))

theorem weakEquivalence_joinMap_id_left (T : DiagSet.{u}) {Y Y' : DiagSet.{u}} (g : Y ⟶ Y')
    [hg : WeakEquivalence ((DiagSet.toInfty 1).map g)] :
    WeakEquivalence ((DiagSet.toInfty 1).map (joinMap (𝟙 T) g)) := by
  exact (weakEquivalences_under_iff _ _).1
    ((isQuillen_joinLeftUnder T).weakEquivalence_map ((DiagSet.toInfty 1).map g))

end Atoms.Diagrammatic
