import Atoms.ForMathlib.CategoryTheory.Subfunctor.Elements
import Atoms.TestCategory.Nerve.Adjunction
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

open CategoryTheory Limits MorphismProperty Opposite

namespace Atoms.TestCategory

universe u

variable (A : Type u) [SmallCategory A]

theorem exists_extension_nerveFunctor_obj (C : Cat.{u, u}) [HasTerminal C]
    {K X : Aᵒᵖ ⥤ Type u} (i : K ⟶ X) [Mono i] (g : K ⟶ (nerveFunctor A).obj C) :
    ∃ g' : X ⟶ (nerveFunctor A).obj C, i ≫ g' = g := by
  let u : (K.Elements)ᵒᵖ ⥤ C := (((nerveAdjunction A).homEquiv K C).symm g).toFunctor
  let e : (elementsFunctor A).obj X ⟶ C := (NatTrans.extendElementsFunctor i u).toCatHom
  refine ⟨(nerveAdjunction A).homEquiv X C e, ?_⟩
  rw [← Adjunction.homEquiv_naturality_left, ← Equiv.eq_symm_apply]
  exact Cat.Hom.ext (NatTrans.mapElements_op_comp_extendElementsFunctor i u)

theorem rlp_terminal_from_nerveFunctor_obj (C : Cat.{u, u}) [HasTerminal C] :
    (monomorphisms (Aᵒᵖ ⥤ Type u)).rlp (terminal.from ((nerveFunctor A).obj C)) := by
  intro K X i hi
  have : Mono i := hi
  refine ⟨fun {t b} sq => ?_⟩
  obtain ⟨g', hg'⟩ := exists_extension_nerveFunctor_obj A C i t
  exact ⟨⟨{ l := g', fac_left := hg', fac_right := terminal.hom_ext _ _ }⟩⟩

theorem rlp_prod_fst_nerveFunctor_obj (C : Cat.{u, u}) [HasTerminal C]
    (X : Aᵒᵖ ⥤ Type u) :
    (monomorphisms (Aᵒᵖ ⥤ Type u)).rlp
      (FunctorToTypes.prod.fst (F := X) (G := (nerveFunctor A).obj C)) := by
  intro K Y i hi
  have : Mono i := hi
  refine ⟨fun {t b} sq => ?_⟩
  obtain ⟨g', hg'⟩ := exists_extension_nerveFunctor_obj A C i (t ≫ FunctorToTypes.prod.snd)
  have hl : i ≫ FunctorToTypes.prod.lift b g' = t := by
    ext a y
    · exact (congrArg (fun φ => φ.app a y) sq.w).symm
    · exact congrArg (fun φ => φ.app a y) hg'
  exact ⟨⟨⟨FunctorToTypes.prod.lift b g', hl, FunctorToTypes.prod.lift_fst _ _⟩⟩⟩

end Atoms.TestCategory
