import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.MappingSpaceOp
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.Op
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Op
import Atoms.Homotopical.Simplicial.CommaLimit
import Atoms.Homotopical.Simplicial.Joyal

open CategoryTheory Limits MorphismProperty Simplicial HomotopicalAlgebra MonoidalCategory

universe u

namespace SSet.modelCategoryJoyal

open Atoms.Homotopical

private noncomputable def cylinderOpIso (Y : SSet.{u}) :
    opFunctor.obj (joyalInterval.cylinder.I.obj Y) ≅ joyalInterval.cylinder.I.obj Y.op :=
  (Functor.Monoidal.μIso opFunctor coherentIso Y).symm ≪≫ whiskerRightIso coherentIsoOpIso Y.op

private theorem endpoint_app_op (ε : Bool) (Y : SSet.{u}) :
    (joyalInterval.cylinder.endpoint ε).app Y.op =
      opFunctor.map ((joyalInterval.cylinder.endpoint ε).app Y) ≫ (cylinderOpIso Y).hom := by
  ext n y
  refine Prod.ext ?_ rfl
  refine CategoryTheory.Functor.ext (fun k ↦ ?_) (fun _ _ _ ↦ rfl)
  exact (joyalPoint_app_obj ε n _ k).trans (joyalPoint_app_obj ε _ _ k.rev).symm

private theorem elementaryHomotopy_opFunctor_map {A B : SSet.{u}} {f g : A ⟶ B}
    (h : joyalInterval.cylinder.ElementaryHomotopy f g) :
    joyalInterval.cylinder.ElementaryHomotopy (opFunctor.map f) (opFunctor.map g) := by
  obtain ⟨k, h₀, h₁⟩ := h
  refine ⟨(cylinderOpIso A).inv ≫ opFunctor.map k, ?_, ?_⟩
  · rw [endpoint_app_op, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, h₀]
  · rw [endpoint_app_op, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, h₁]

theorem homotopic_opFunctor_map_iff {A B : SSet.{u}} (f g : A ⟶ B) :
    joyalInterval.cylinder.Homotopic (opFunctor.map f) (opFunctor.map g) ↔
      joyalInterval.cylinder.Homotopic f g := by
  refine ⟨fun h ↦ ?_, ExactCylinder.Homotopic.map _ _ fun _ _ ↦ elementaryHomotopy_opFunctor_map⟩
  have h' := ExactCylinder.Homotopic.map _ _ (fun _ _ ↦ elementaryHomotopy_opFunctor_map) h
  have e (u : A ⟶ B) : u = opFunctorCompOpFunctorIso.inv.app A ≫
      opFunctor.map (opFunctor.map u) ≫ opFunctorCompOpFunctorIso.hom.app B :=
    (opFunctorCompOpFunctorIso.inv_hom_id_app_assoc A u).symm.trans
      (congrArg _ (opFunctorCompOpFunctorIso.hom.naturality u).symm)
  rw [e f, e g]
  exact joyalInterval.cylinder.homotopic_precomp _ (joyalInterval.cylinder.homotopic_comp h' _)

private noncomputable def homotopyClassesOpEquiv (A Z : SSet.{u}) :
    joyalInterval.cylinder.HomotopyClasses A Z ≃
      joyalInterval.cylinder.HomotopyClasses A.op Z.op :=
  Quotient.congr opEquivalence.fullyFaithfulFunctor.homEquiv fun u v ↦
    (homotopic_opFunctor_map_iff u v).symm

private theorem homotopyClassesOpEquiv_comp_precompClasses {A B : SSet.{u}} (f : A ⟶ B)
    (Z : SSet.{u}) :
    homotopyClassesOpEquiv A Z ∘ joyalInterval.cylinder.precompClasses f Z =
      joyalInterval.cylinder.precompClasses (opFunctor.map f) Z.op ∘
        homotopyClassesOpEquiv B Z := by
  funext c
  induction c using Quotient.inductionOn with | h u => ?_
  exact congrArg (Quotient.mk _) (opFunctor.map_comp f u)

private theorem isFibrant_op {Z : SSet.{u}}
    (hZ : joyalInterval.{u}.cylinder.IsFibrant SSet.innerHornInclusions Z) :
    joyalInterval.{u}.cylinder.IsFibrant SSet.innerHornInclusions Z.op := by
  rw [← ExactCylinder.modelCategory.isFibrant_iff _ _ SSet.innerHornInclusions_le_monomorphisms,
    isFibrant_iff_quasicategory] at hZ ⊢
  infer_instance

private theorem weakEquivalence_of_weakEquivalence_opFunctor_map {A B : SSet.{u}} (f : A ⟶ B)
    (h : WeakEquivalence (opFunctor.map f)) : WeakEquivalence f := by
  rw [weakEquivalence_iff] at h ⊢
  intro (Z : SSet.{u}) hZ
  rw [← (homotopyClassesOpEquiv A Z).bijective.of_comp_iff',
    homotopyClassesOpEquiv_comp_precompClasses]
  exact (h (opFunctor.obj Z) (isFibrant_op hZ)).comp (homotopyClassesOpEquiv B Z).bijective

theorem weakEquivalence_opFunctor_map_iff {A B : SSet.{u}} (f : A ⟶ B) :
    WeakEquivalence (opFunctor.map f) ↔ WeakEquivalence f := by
  refine ⟨weakEquivalence_of_weakEquivalence_opFunctor_map f, fun h ↦ ?_⟩
  refine weakEquivalence_of_weakEquivalence_opFunctor_map _ ?_
  rw [weakEquivalence_iff] at h ⊢
  exact ((weakEquivalences _).arrow_mk_iso_iff
    (Arrow.isoOfNatIso opFunctorCompOpFunctorIso (Arrow.mk f))).2 h

theorem trivialCofibration_opFunctor_map_iff {A B : SSet.{u}} (f : A ⟶ B) :
    trivialCofibrations SSet.{u} (opFunctor.map f) ↔ trivialCofibrations SSet.{u} f := by
  rw [mem_trivialCofibrations_iff, mem_trivialCofibrations_iff, cofibration_iff, cofibration_iff,
    weakEquivalence_opFunctor_map_iff]
  exact and_congr_left' (Functor.mono_map_iff_mono opFunctor f)

theorem fibration_opFunctor_map_iff {X Y : SSet.{u}} (p : X ⟶ Y) :
    Fibration (opFunctor.map p) ↔ Fibration p := by
  rw [fibration_iff, fibration_iff, ← trivialCofibrations_rlp]
  exact rlp_opFunctor_map_iff (fun _ _ i hi ↦ (trivialCofibration_opFunctor_map_iff i).2 hi) p

end SSet.modelCategoryJoyal

namespace SSet

open modelCategoryJoyal in
theorem isInitialObject_iff_of_weakEquivalence {X Y : SSet.{u}} [X.Quasicategory]
    [Y.Quasicategory] (F : X ⟶ Y) [WeakEquivalence F] (x : X _⦋0⦌) :
    IsInitialObject (F.app _ x) ↔ IsInitialObject x := by
  have : WeakEquivalence (opFunctor.map F) := (weakEquivalence_opFunctor_map_iff F).2 ‹_›
  exact isFinal_iff_of_weakEquivalence (opFunctor.map F) (opObjEquiv.symm x)

open modelCategoryJoyal in
theorem isZeroObject_iff_of_weakEquivalence {X Y : SSet.{u}} [X.Quasicategory]
    [Y.Quasicategory] (F : X ⟶ Y) [WeakEquivalence F] (x : X _⦋0⦌) :
    IsZeroObject (F.app _ x) ↔ IsZeroObject x :=
  and_congr (isFinal_iff_of_weakEquivalence F x) (isInitialObject_iff_of_weakEquivalence F x)

open modelCategoryJoyal in
theorem isInitialObject_iff_mappingSpace {X : SSet.{u}} [X.Quasicategory] (ω : X _⦋0⦌) :
    IsInitialObject ω ↔ ∀ x : X _⦋0⦌,
      modelCategoryQuillen.I.rlp (stdSimplex.isTerminalObj₀.from (mappingSpace X ω x)) := by
  rw [IsInitialObject, isFinal_iff_mappingSpace]
  refine (opObjEquiv (X := X)).forall_congr_left.trans (forall_congr' fun x ↦ ?_)
  exact (((modelCategoryQuillen.I.rlp).cancel_left_of_respectsIso
    (mappingSpaceOpIso X ω x).hom _).symm.trans
      (iff_of_eq (congrArg _ (stdSimplex.isTerminalObj₀.hom_ext _ _)))).trans
    (((modelCategoryQuillen.I.rlp).cancel_right_of_respectsIso
      (opFunctor.map (stdSimplex.isTerminalObj₀.from (mappingSpace X ω x)))
      (stdSimplex.opIso ⦋0⦌).hom).trans (rlp_I_opFunctor_map_iff _))

end SSet
