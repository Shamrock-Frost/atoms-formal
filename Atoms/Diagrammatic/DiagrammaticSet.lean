import Atoms.Homotopical.EilenbergZilber.RigidCellularModel
import Atoms.Shape.Rigidity
import Atoms.Shape.Standard
import Atoms.TestCategory.BasicLocalizer.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Dense
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

open CategoryTheory Limits Opposite Atoms.Shape

universe u

namespace Atoms.Diagrammatic

instance : Homotopical.HasTrivialAutomorphisms Atom := ⟨fun _ ↦ ⟨Atom.iso_eq⟩⟩

instance ezCategoryAtom : Homotopical.EZCategory Atom :=
  Homotopical.EZCategory.ofCollapseInclusion (fun U ↦ U.dimension) collapses inclusions
    (fun _ _ p hp ↦ isSplitEpi_of_isCollapseHom p hp) (fun _ _ i hi ↦ mono_of_isInclusionHom i hi)
    (fun _ _ i hi ↦ dimension_le_of_isInclusionHom i hi)
    (fun _ _ i hi h ↦ isIso_of_isInclusionHom_of_dimension_eq i hi h)
    (fun _ _ f ↦ exists_collapse_inclusion_factorization f)
    (fun _ _ p q hp _ h ↦ eq_of_isCollapseHom_of_forall_section_iff p q hp h)

theorem collapses_eq_splitEpimorphisms :
    collapses = MorphismProperty.splitEpimorphisms Atom :=
  le_antisymm (fun _ _ p hp => isSplitEpi_of_isCollapseHom p hp)
    fun _ _ p hp => @isCollapseHom_of_isSplitEpi _ _ p hp

theorem inclusions_eq_monomorphisms :
    inclusions = MorphismProperty.monomorphisms Atom :=
  le_antisymm (fun _ _ i hi => mono_of_isInclusionHom i hi)
    fun _ _ f hf => @isInclusionHom_of_mono _ _ f hf

abbrev DiagSet : Type (u + 1) := Atomᵒᵖ ⥤ Type u

abbrev diagram (X : DiagSet.{u}) (U : Atom) : Type u := X.obj (op U)

abbrev ball (U : Atom) : DiagSet.{u} := uliftYoneda.{u}.obj U

def ballMap {U V : Atom} (f : U ⟶ V) : ball.{u} U ⟶ ball V :=
  uliftYoneda.map f

@[simp] theorem ballMap_id (U : Atom) : ballMap.{u} (𝟙 U) = 𝟙 (ball U) :=
  uliftYoneda.map_id U

@[simp] theorem ballMap_comp {U V W : Atom} (f : U ⟶ V) (g : V ⟶ W) :
    ballMap.{u} (f ≫ g) = ballMap f ≫ ballMap g :=
  uliftYoneda.map_comp f g

@[simp] theorem ballMap_app {U V T : Atom} (f : U ⟶ V) (g : T ⟶ U) :
    (ballMap.{u} f).app (op T) (ULift.up g) = ULift.up (g ≫ f) := rfl

def isTerminalBallAtomPoint : IsTerminal (ball.{u} atomPoint) :=
  IsTerminal.ofUniqueHom
    (fun _ => { app := fun T => TypeCat.ofHom fun _ => ⟨toAtomPoint T.unop⟩ })
    fun _ _ => by
      ext
      exact ULift.ext _ _ (Subsingleton.elim (α := _ ⟶ atomPoint) _ _)

def sphere (U : Atom) : DiagSet.{u} :=
  (Homotopical.EZCategory.uliftBoundary.{u} U).toFunctor

def sphereInclusion (U : Atom) : sphere.{u} U ⟶ ball.{u} U :=
  (Homotopical.EZCategory.uliftBoundary.{u} U).ι

instance mono_sphereInclusion (U : Atom) : Mono (sphereInclusion.{u} U) :=
  inferInstanceAs (Mono (Homotopical.EZCategory.uliftBoundary.{u} U).ι)

noncomputable def DiagSet.isInitialSphereOfDimensionEqZero (U : Atom)
    (hU : U.dimension = 0) : IsInitial (sphere.{u} U) := by
  have := isIso_toAtomPoint_of_dimension_eq_zero hU
  have hempty (T : Atomᵒᵖ) (x : (sphere.{u} U).obj T) : False := by
    apply (Homotopical.EZCategory.mem_uliftBoundary_iff x.val).1 x.property
    have hx : x.val.down = toAtomPoint T.unop ≫ inv (toAtomPoint U) :=
      (IsIso.eq_comp_inv _).2 (isTerminalAtomPoint.hom_ext _ _)
    rw [hx]
    have : IsSplitEpi (toAtomPoint T.unop) :=
      isSplitEpi_of_isCollapseHom _ (isCollapseHom_toAtomPoint _)
    infer_instance
  exact IsInitial.ofUniqueHom
    (fun _ => { app := fun T => TypeCat.ofHom fun x => False.elim (hempty T x)
                naturality := fun {T V} _ => by ext x; exact False.elim (hempty T x) })
    (fun _ _ => by ext T x; exact False.elim (hempty T x))

def sphereInclusions : MorphismProperty DiagSet.{u} :=
  MorphismProperty.ofHoms fun U : Atom => sphereInclusion.{u} U

section Extension

variable {E : Type*} [Category.{u} E]

noncomputable def isoOfPreservesColimits (F G : DiagSet.{u} ⥤ E)
    [PreservesColimitsOfSize.{0, u} F] [PreservesColimitsOfSize.{0, u} G]
    (e : uliftYoneda.{u} ⋙ F ≅ uliftYoneda.{u} ⋙ G) : F ≅ G :=
  have := Presheaf.isLeftKanExtension_of_preservesColimits F (Iso.refl _)
  have := Presheaf.isLeftKanExtension_of_preservesColimits G (Iso.refl _)
  Functor.leftKanExtensionUniqueOfIso F (Iso.refl _).hom e G (Iso.refl _).hom

theorem isoOfPreservesColimits_hom_app (F G : DiagSet.{u} ⥤ E)
    [PreservesColimitsOfSize.{0, u} F] [PreservesColimitsOfSize.{0, u} G]
    (e : uliftYoneda.{u} ⋙ F ≅ uliftYoneda.{u} ⋙ G) (U : Atom) :
    (isoOfPreservesColimits F G e).hom.app (uliftYoneda.obj U) = e.hom.app U := by
  have := Presheaf.isLeftKanExtension_of_preservesColimits F (Iso.refl _)
  have h := F.descOfIsLeftKanExtension_fac_app (Iso.refl _).hom G (e.hom ≫ (Iso.refl _).hom) U
  refine Eq.trans ?_ (h.trans (by simp))
  simp [isoOfPreservesColimits]

theorem hom_ext_of_preservesColimits {F G : DiagSet.{u} ⥤ E}
    [PreservesColimitsOfSize.{0, u} F] {α β : F ⟶ G}
    (h : ∀ U : Atom, α.app (uliftYoneda.obj U) = β.app (uliftYoneda.obj U)) : α = β := by
  have := Presheaf.isLeftKanExtension_of_preservesColimits F (Iso.refl (uliftYoneda.{u} ⋙ F))
  refine F.hom_ext_of_isLeftKanExtension (Iso.refl (uliftYoneda.{u} ⋙ F)).hom α β ?_
  ext U
  simpa using h U

end Extension

instance isSmall_sphereInclusions : MorphismProperty.IsSmall.{u} sphereInclusions.{u} :=
  MorphismProperty.isSmall_ofHoms _

theorem monomorphisms_eq_saturation_sphereInclusions :
    MorphismProperty.monomorphisms DiagSet.{u} =
      MorphismProperty.saturation.{u} sphereInclusions.{u} :=
  Homotopical.EZCategory.monomorphisms_eq_saturation_boundaryInclusions

def IsDegenerate (X : DiagSet.{u}) {U : Atom} (x : diagram X U) : Prop :=
  ∃ (V : Atom) (p : U ⟶ V) (y : diagram X V),
    IsCollapseHom p ∧ ¬ IsIso p ∧ X.map p.op y = x

theorem isDegenerate_iff_not_isNondegenerate (X : DiagSet.{u}) {U : Atom} (x : diagram X U) :
    IsDegenerate X x ↔ ¬ Homotopical.EZCategory.IsNondegenerate X x := by
  constructor
  · rintro ⟨V, p, y, hp, hiso, hy⟩ hx
    exact hiso (hx p (isSplitEpi_of_isCollapseHom p hp) ⟨y, hy⟩)
  · intro hx
    simp only [Homotopical.EZCategory.IsNondegenerate, not_forall] at hx
    obtain ⟨V, p, hp, ⟨y, hy⟩, hiso⟩ := hx
    exact ⟨V, p, y, @isCollapseHom_of_isSplitEpi _ _ p hp, hiso, hy⟩

theorem isDegenerate_map_of_dimension_eq_zero {Y : DiagSet.{u}} {S W : Atom} (p : S ⟶ W)
    (hW : W.dimension = 0) (hS : 0 < S.dimension) (y : diagram Y W) :
    IsDegenerate Y (Y.map p.op y) := by
  have := isIso_toAtomPoint_of_dimension_eq_zero hW
  have hp : toAtomPoint S ≫ inv (toAtomPoint W) = p := by
    rw [IsIso.comp_inv_eq]
    exact Subsingleton.elim _ _
  refine ⟨atomPoint, toAtomPoint S, Y.map (inv (toAtomPoint W)).op y,
    isCollapseHom_toAtomPoint S, fun h => ?_, ?_⟩
  · have := Atom.dimension_eq_of_iso (asIso (toAtomPoint S))
    rw [dimension_atomPoint] at this
    omega
  · rw [← Functor.map_comp_apply, ← op_comp, hp]

theorem isDegenerate_of_isDegenerate_app {P P' : DiagSet.{u}} (f : P ⟶ P') [Mono f]
    {V : Atom} {c : diagram P V} (h : IsDegenerate P' (f.app (op V) c)) : IsDegenerate P c := by
  have hinj : ∀ U, Function.Injective (f.app (op U)) := fun U =>
    (mono_iff_injective (f.app (op U))).1 (inferInstance)
  obtain ⟨W, p, y, hp, hni, hy⟩ := h
  obtain ⟨σ, hσ⟩ : ∃ σ : W ⟶ V, σ ≫ p = 𝟙 W :=
    ⟨(isSplitEpi_of_isCollapseHom p hp).exists_splitEpi.some.section_,
      (isSplitEpi_of_isCollapseHom p hp).exists_splitEpi.some.id⟩
  have hy' : f.app (op W) (P.map σ.op c) = y :=
    (NatTrans.naturality_apply f σ.op c).trans ((congrArg (P'.map σ.op) hy.symm).trans
      ((Functor.map_comp_apply P' p.op σ.op y).symm.trans
        ((congrArg (fun r : W ⟶ W => P'.map r.op y) hσ).trans (Functor.map_id_apply P' (op W) y))))
  exact ⟨W, p, P.map σ.op c, hp, hni, hinj V ((NatTrans.naturality_apply f p.op _).trans
    ((congrArg (P'.map p.op) hy').trans hy))⟩

def DiagSet.asSmall : DiagSet.{u} ⥤ ((AsSmall.{u} Atom)ᵒᵖ ⥤ Type u) :=
  (Functor.whiskeringLeft (AsSmall.{u} Atom)ᵒᵖ Atomᵒᵖ (Type u)).obj AsSmall.down.op

def DiagSet.asSmallEquivalence : DiagSet.{u} ≌ ((AsSmall.{u} Atom)ᵒᵖ ⥤ Type u) :=
  (AsSmall.equiv : Atom ≌ AsSmall.{u} Atom).op.congrLeft

instance : DiagSet.asSmall.{u}.IsEquivalence :=
  DiagSet.asSmallEquivalence.isEquivalence_functor

def DiagSet.asSmallBallIso (U : Atom) :
    DiagSet.asSmall.{u}.obj (ball U) ≅ yoneda.obj (AsSmall.up.obj U) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl

end Atoms.Diagrammatic

namespace Atoms.TestCategory.BasicLocalizer

theorem aspherical_atom (𝒲 : BasicLocalizer.{0}) : 𝒲.Aspherical (Cat.of Atom) :=
  𝒲.terminal_aspherical (Cat.of Atom)

theorem aspherical_asSmallAtom (𝒲 : BasicLocalizer.{u}) :
    𝒲.Aspherical (Cat.of (AsSmall.{u} Atom)) :=
  𝒲.terminal_aspherical (Cat.of (AsSmall.{u} Atom))

end Atoms.TestCategory.BasicLocalizer
