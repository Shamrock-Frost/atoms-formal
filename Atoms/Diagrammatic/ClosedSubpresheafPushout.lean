import Atoms.Diagrammatic.ClosedSubpresheaf
import Atoms.ForMathlib.CategoryTheory.Subfunctor.Colimits

open CategoryTheory Limits Opposite Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

theorem closedSubpresheaf_univ (U : Atom) : closedSubpresheaf.{u} U ⊤ = ⊤ := by
  ext ⟨T⟩ ⟨f : T ⟶ U⟩
  exact ⟨fun _ => trivial, fun _ _ => LowerSet.mem_top⟩

theorem closedSubpresheaf_inter (U : Atom) (A B : LowerSet U.ogp) :
    closedSubpresheaf.{u} U A ⊓ closedSubpresheaf U B = closedSubpresheaf U (A ⊓ B) := by
  ext ⟨T⟩ ⟨f : T ⟶ U⟩
  exact ⟨fun h t => ⟨h.1 t, h.2 t⟩,
    fun h => ⟨fun t => (h t).1, fun t => (h t).2⟩⟩

theorem isPushout_closedSubpresheaf (U : Atom) (A B : LowerSet U.ogp) :
    IsPushout
      (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} U (inf_le_left (a := A) (b := B))))
      (Subfunctor.homOfLe (closedSubpresheaf_mono U (inf_le_right (a := A) (b := B))))
      (Subfunctor.homOfLe (closedSubpresheaf_mono U (le_sup_left (a := A) (b := B))))
      (Subfunctor.homOfLe (closedSubpresheaf_mono U (le_sup_right (a := A) (b := B)))) :=
  Subfunctor.isPushout_of_bicartSq
    ⟨(closedSubpresheaf_union U A B).symm, closedSubpresheaf_inter U A B⟩

theorem exists_apply_eq_of_mem_closedSubpresheaf_image {V U T : Atom} (f : V ⟶ U)
    {S : LowerSet V.ogp} {g : T ⟶ U}
    (hg : ULift.up g ∈ (closedSubpresheaf.{u} U (Atom.map f S)).obj (op T)) (t : T.ogp) :
    ∃ a, f a = g t := by
  obtain ⟨a, -, ha⟩ := hg t
  exact ⟨a, ha⟩

theorem liftOfIsInclusionHom_mem_closedSubpresheaf {V U T : Atom} (f : V ⟶ U)
    (hf : IsInclusionHom f) {S : LowerSet V.ogp} {g : T ⟶ U}
    (hg : ULift.up g ∈ (closedSubpresheaf.{u} U (Atom.map f S)).obj (op T)) :
    ULift.up (liftOfIsInclusionHom f hf g (exists_apply_eq_of_mem_closedSubpresheaf_image f hg)) ∈
      (closedSubpresheaf.{u} V S).obj (op T) := by
  intro t
  obtain ⟨a, ha, hfa⟩ := hg t
  have hc := congrArg (fun k : T ⟶ U => k t)
    (liftOfIsInclusionHom_comp f hf g (exists_apply_eq_of_mem_closedSubpresheaf_image f hg))
  simp only [ConcreteCategory.comp_apply] at hc
  rw [hf (hc.trans hfa.symm)]
  exact ha

noncomputable def closedSubpresheafImageIso {V U : Atom} (f : V ⟶ U) (hf : IsInclusionHom f)
    (S : LowerSet V.ogp) :
    (closedSubpresheaf.{u} V S).toFunctor ≅ (closedSubpresheaf U (Atom.map f S)).toFunctor :=
  NatIso.ofComponents
    (fun T => Equiv.toIso
      { toFun := fun g => ⟨⟨g.1.down ≫ f⟩, fun t => Set.mem_image_of_mem _ (g.2 t)⟩
        invFun := fun g => ⟨⟨liftOfIsInclusionHom f hf g.1.down
            (exists_apply_eq_of_mem_closedSubpresheaf_image f g.2)⟩,
          liftOfIsInclusionHom_mem_closedSubpresheaf f hf g.2⟩
        left_inv := fun g => by
          have := mono_of_isInclusionHom f hf
          exact Subtype.ext (ULift.ext _ _ ((cancel_mono f).1
            (liftOfIsInclusionHom_comp f hf (g.1.down ≫ f) fun t =>
              ⟨ConcreteCategory.hom g.1.down t, rfl⟩)))
        right_inv := fun g => Subtype.ext (ULift.ext _ _ (liftOfIsInclusionHom_comp f hf g.1.down
          (exists_apply_eq_of_mem_closedSubpresheaf_image f g.2))) })
    (fun _ => rfl)

theorem closedSubpresheafImageIso_hom_comp_ι {V U : Atom} (f : V ⟶ U) (hf : IsInclusionHom f)
    (S : LowerSet V.ogp) :
    (closedSubpresheafImageIso f hf S).hom ≫ (closedSubpresheaf U (Atom.map f S)).ι =
      (closedSubpresheaf V S).ι ≫ uliftYoneda.{u}.map f := by
  ext T g
  rfl

noncomputable def homOfLeImageArrowIso {V U : Atom} (f : V ⟶ U) (hf : IsInclusionHom f)
    {S S' : LowerSet V.ogp} (h : S ≤ S') {B C : LowerSet U.ogp} (hBC : B ≤ C)
    (hB : Atom.map f S = B) (hC : Atom.map f S' = C) :
    Arrow.mk (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} V h)) ≅
      Arrow.mk (Subfunctor.homOfLe (closedSubpresheaf_mono U hBC)) := by
  subst hB hC
  refine Arrow.isoMk (closedSubpresheafImageIso f hf S) (closedSubpresheafImageIso f hf S') ?_
  ext T g
  rfl

noncomputable def homOfLeUnivArrowIso (V : Atom) (S : LowerSet V.ogp) :
    Arrow.mk (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} V (le_top : S ≤ ⊤))) ≅
      Arrow.mk (closedSubpresheaf V S).ι :=
  have hι : IsIso (closedSubpresheaf V ⊤).ι :=
    (Subfunctor.eq_top_iff_isIso _).1 (closedSubpresheaf_univ V)
  Arrow.isoMk (Iso.refl _) (@asIso _ _ _ _ (closedSubpresheaf V ⊤).ι hι)
    ((Category.id_comp _).trans
      (Subfunctor.homOfLe_ι (closedSubpresheaf_mono V (le_top : S ≤ ⊤))).symm)

end Atoms.Diagrammatic
