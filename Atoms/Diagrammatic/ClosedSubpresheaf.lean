import Atoms.Diagrammatic.DiagrammaticSet

open CategoryTheory Limits Opposite Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

abbrev Atom.map {V U : Atom} (f : V ⟶ U) (S : LowerSet V.ogp) : LowerSet U.ogp :=
  ⟨f '' S, (Atom.isMap f).fibration.isLowerSet_image S.lower⟩

theorem Atom.map_top {V U : Atom} (f : V ⟶ U) : Atom.map f ⊤ = LowerSet.Iic (f V.top) :=
  SetLike.coe_injective (by
    change f '' ((⊤ : LowerSet V.ogp) : Set V.ogp) = Set.Iic (f V.top)
    rw [← V.Iic_top, LowerSet.coe_Iic, (Atom.isMap f).image_Iic])

theorem Atom.map_top_eq_Iic_iff {V U : Atom} {f : V ⟶ U} {a : U.ogp} :
    Atom.map f ⊤ = LowerSet.Iic a ↔ Set.range f = Set.Iic a := by
  rw [← SetLike.coe_set_eq, LowerSet.coe_Iic]
  change f '' Set.univ = _ ↔ _
  rw [Set.image_univ]

def closedSubpresheaf (U : Atom) (S : LowerSet U.ogp) : Subfunctor (ball.{u} U) where
  obj T := {f : ULift.{u} (T.unop ⟶ U) | ∀ t, f.down t ∈ S}
  map g _ hf := fun t => hf (g.unop t)

theorem mem_closedSubpresheaf_iff (U : Atom) (S : LowerSet U.ogp) {T : Atom}
    (f : T ⟶ U) : ULift.up f ∈ (closedSubpresheaf.{u} U S).obj (Opposite.op T) ↔ ∀ t, f t ∈ S :=
  Iff.rfl

theorem closedSubpresheaf_univ_erase_top (U : Atom) :
    closedSubpresheaf U (U.ogp.bdryFull ⊤) = Homotopical.EZCategory.uliftBoundary.{u} U := by
  ext ⟨T⟩ ⟨f : T ⟶ U⟩
  change (∀ t, f t ∈ U.ogp.bdryFull ⊤) ↔ ¬ IsSplitEpi f
  simp only [U.mem_bdryFull_top_iff]
  constructor
  · intro hf hsplit
    obtain ⟨t, ht⟩ := isCollapseHom_of_isSplitEpi f U.top
    exact hf t ht
  · intro hf t ht
    exact hf (isSplitEpi_of_isCollapseHom f (isCollapseHom_of_apply_eq_top f ht))

private theorem range_le_closedSubpresheaf (U : Atom) (S : LowerSet U.ogp) (x : S) :
    Subfunctor.range (uliftYoneda.{u}.map (Atom.closureIncl U x.1)) ≤ closedSubpresheaf U S := by
  rintro ⟨T⟩ _ ⟨⟨g⟩, rfl⟩
  exact comp_closureIncl_mem U S x g

def principalCocone (U : Atom) (S : LowerSet U.ogp) :
    Limits.Cocone (principalDiagram U S ⋙ uliftYoneda.{u}) where
  pt := (closedSubpresheaf U S).toFunctor
  ι :=
    { app x := Subfunctor.lift (uliftYoneda.{u}.map (Atom.closureIncl U x.1))
        (range_le_closedSubpresheaf U S x)
      naturality _ _ f :=
        (cancel_mono (closedSubpresheaf U S).ι).1 <|
          ((Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) (Subfunctor.lift_ι _ _)).trans <|
            (uliftYoneda.{u}.map_comp _ _).symm.trans <|
              congrArg uliftYoneda.{u}.map (principalMap_comp_closureIncl U (leOfHom f))).trans
          ((Subfunctor.lift_ι _ _).symm.trans (congrArg (· ≫ _) (Category.comp_id _).symm)) }

theorem principalCocone_ι_app_comp_ι (U : Atom) (S : LowerSet U.ogp) (x : S) :
    (principalCocone.{u} U S).ι.app x ≫ (closedSubpresheaf U S).ι =
      uliftYoneda.{u}.map (Atom.closureIncl U x.1) :=
  rfl

theorem ιColimitType_eq_ιColimitType_principalLift (U : Atom) (S : LowerSet U.ogp)
    (T : Atom) (x : S) (g : T ⟶ Atom.ofClosure U x.1) (f : T ⟶ U)
    (hf : ∀ t, f t ∈ S) (hgf : g ≫ Atom.closureIncl U x.1 = f) :
    ((principalDiagram U S ⋙ uliftYoneda.{u}) ⋙
        (evaluation Atomᵒᵖ (Type u)).obj (op T)).ιColimitType x ⟨g⟩ =
      ((principalDiagram U S ⋙ uliftYoneda.{u}) ⋙
        (evaluation Atomᵒᵖ (Type u)).obj (op T)).ιColimitType
        ⟨f T.top, hf _⟩ ⟨principalLift U (f T.top) f (apply_mem_closure_apply_top f)⟩ := by
  subst hgf
  have hzx : (g ≫ Atom.closureIncl U x.1) T.top ≤ x.1 := by
    rw [ConcreteCategory.comp_apply]
    exact closureIncl_mem_closure U x.1 (g T.top)
  refine (Functor.ιColimitType_eq_iff _ _ _).2
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨homOfLE hzx, ?_⟩))
  change ULift.up g = ULift.up (principalLift U _ (g ≫ Atom.closureIncl U x.1)
    (apply_mem_closure_apply_top _) ≫ principalMap U (leOfHom (homOfLE hzx)))
  exact congrArg ULift.up ((hom_ext_closureIncl U x.1 (principalLift_comp_closureIncl U x.1 _
    fun t => closureIncl_mem_closure U x.1 (g t)).symm).trans
    (principalLift_comp_principalMap U _ _ _ _).symm)

theorem bijective_descColimitType_principalCocone (U : Atom) (S : LowerSet U.ogp) (T : Atomᵒᵖ) :
    Function.Bijective (Functor.descColimitType _
      ((Functor.coconeTypesEquiv _).symm
        (((evaluation Atomᵒᵖ (Type u)).obj T).mapCocone (principalCocone U S)))) := by
  induction T with | op T => ?_
  refine ⟨fun a b hab => ?_, ?_⟩
  · obtain ⟨x, ⟨g⟩, rfl⟩ := Functor.ιColimitType_jointly_surjective _ a
    obtain ⟨y, ⟨g'⟩, rfl⟩ := Functor.ιColimitType_jointly_surjective _ b
    change T ⟶ Atom.ofClosure U x.1 at g
    change T ⟶ Atom.ofClosure U y.1 at g'
    change (⟨⟨g ≫ Atom.closureIncl U x.1⟩, comp_closureIncl_mem U S x g⟩ :
        (closedSubpresheaf U S).obj (op T)) =
      ⟨⟨g' ≫ Atom.closureIncl U y.1⟩, comp_closureIncl_mem U S y g'⟩ at hab
    have h : g ≫ Atom.closureIncl U x.1 = g' ≫ Atom.closureIncl U y.1 :=
      congrArg ULift.down (Subtype.mk.inj hab)
    have e1 := ιColimitType_eq_ιColimitType_principalLift U S T x g
      (g' ≫ Atom.closureIncl U y.1) (comp_closureIncl_mem U S y g') h
    have e2 := ιColimitType_eq_ιColimitType_principalLift U S T y g'
      (g' ≫ Atom.closureIncl U y.1) (comp_closureIncl_mem U S y g') rfl
    exact e1.trans e2.symm
  · intro p
    change (closedSubpresheaf U S).obj (op T) at p
    obtain ⟨⟨f : T ⟶ U⟩, hf⟩ := p
    refine ⟨((principalDiagram U S ⋙ uliftYoneda.{u}) ⋙
      (evaluation Atomᵒᵖ (Type u)).obj (op T)).ιColimitType ⟨f T.top, hf _⟩
      ⟨principalLift U (f T.top) f (apply_mem_closure_apply_top f)⟩, ?_⟩
    exact Subtype.ext (congrArg ULift.up (principalLift_comp_closureIncl U (f T.top) f _))

noncomputable def isColimitPrincipalCocone (U : Atom) (S : LowerSet U.ogp) :
    Limits.IsColimit (principalCocone.{u} U S) :=
  evaluationJointlyReflectsColimits _ fun T => Nonempty.some <|
    (Types.isColimit_iff_coconeTypesIsColimit _).2
      ⟨bijective_descColimitType_principalCocone U S T⟩

noncomputable def liftOfIsInclusionHom {A W T : Atom} (i : A ⟶ W) (hi : IsInclusionHom i)
    (f : T ⟶ W) (h : ∀ t, ∃ a, i a = f t) : T ⟶ A :=
  haveI := isIso_principalLift_of_isInclusionHom i hi
  principalLift W (i A.top) f (mem_closure_apply_top_of_exists_eq i h) ≫
    inv (principalLift W (i A.top) i (apply_mem_closure_apply_top i))

theorem liftOfIsInclusionHom_comp {A W T : Atom} (i : A ⟶ W) (hi : IsInclusionHom i)
    (f : T ⟶ W) (h : ∀ t, ∃ a, i a = f t) : liftOfIsInclusionHom i hi f h ≫ i = f := by
  have := isIso_principalLift_of_isInclusionHom i hi
  have hc : inv (principalLift W (i A.top) i (apply_mem_closure_apply_top i)) ≫ i =
      Atom.closureIncl W (i A.top) :=
    (IsIso.inv_comp_eq _).2 (principalLift_comp_closureIncl W _ i _).symm
  rw [liftOfIsInclusionHom, Category.assoc, hc, principalLift_comp_closureIncl]

theorem closureIncl_mem_of_mem {U : Atom} (R : Subfunctor (ball.{u} U)) {T : Atom}
    {f : T ⟶ U} (hf : ULift.up f ∈ R.obj (op T)) :
    ULift.up (Atom.closureIncl U (f T.top)) ∈ R.obj (op (Atom.ofClosure U (f T.top))) := by
  have := isSplitEpi_of_isCollapseHom _
    (isCollapseHom_of_apply_eq_top _ (principalLift_apply_top f))
  have h := IsSplitEpi.id_assoc
    (principalLift U (f T.top) f (apply_mem_closure_apply_top f))
    (Atom.closureIncl U (f T.top))
  rw [principalLift_comp_closureIncl] at h
  rw [← h]
  exact R.map (section_ (principalLift U (f T.top) f (apply_mem_closure_apply_top f))).op hf

theorem exists_closedSubpresheaf_eq (U : Atom) (R : Subfunctor (ball.{u} U)) :
    ∃ S : LowerSet U.ogp, closedSubpresheaf U S = R := by
  let S : LowerSet U.ogp :=
    ⟨{x | ULift.up (Atom.closureIncl U x) ∈ R.obj (op (Atom.ofClosure U x))}, fun x y hyx hx => by
      change ULift.up (Atom.closureIncl U y) ∈ R.obj (op (Atom.ofClosure U y))
      rw [← principalMap_comp_closureIncl U hyx]
      exact R.map (principalMap U hyx).op hx⟩
  refine ⟨S, ?_⟩
  ext ⟨T⟩ ⟨f : T ⟶ U⟩
  change (∀ t, f t ∈ S) ↔ ULift.up f ∈ R.obj (op T)
  constructor
  · intro hf
    have hmem : ∀ t, f t ∈ LowerSet.Iic (f T.top) := apply_mem_closure_apply_top f
    rw [← principalLift_comp_closureIncl U (f T.top) f hmem]
    exact R.map (principalLift U (f T.top) f hmem).op (hf T.top)
  · intro hf t
    exact S.lower (apply_mem_closure_apply_top f t) (closureIncl_mem_of_mem R hf)

theorem closedSubpresheaf_mono (U : Atom) {S T : LowerSet U.ogp} (h : S ≤ T) :
    closedSubpresheaf.{u} U S ≤ closedSubpresheaf U T := by
  rintro ⟨V⟩ f hf t
  exact h (hf t)

theorem closedSubpresheaf_union (U : Atom) (S T : LowerSet U.ogp) :
    closedSubpresheaf.{u} U (S ⊔ T) = closedSubpresheaf U S ⊔ closedSubpresheaf U T := by
  refine le_antisymm ?_ (sup_le (closedSubpresheaf_mono U le_sup_left)
    (closedSubpresheaf_mono U le_sup_right))
  rintro ⟨V⟩ g hg
  rw [Subfunctor.max_obj, Set.mem_union]
  rcases LowerSet.mem_sup_iff.1 (hg V.top) with h | h
  · exact Or.inl fun t => S.lower (apply_mem_closure_apply_top g.down t) h
  · exact Or.inr fun t => T.lower (apply_mem_closure_apply_top g.down t) h

theorem range_yoneda_map_of_isInclusionHom {V U : Atom} (f : V ⟶ U) (hf : IsInclusionHom f) :
    Subfunctor.range (uliftYoneda.{u}.map f) = closedSubpresheaf U (Atom.map f ⊤) := by
  ext ⟨T⟩ ⟨g : T ⟶ U⟩
  change (∃ h : ULift.{u} (T ⟶ V), ULift.up (h.down ≫ f) = ULift.up g) ↔ ∀ t, g t ∈ Atom.map f ⊤
  constructor
  · rintro ⟨⟨h⟩, hh⟩ t
    cases hh
    exact ⟨h t, LowerSet.mem_top, rfl⟩
  · intro hg
    have hg' : ∀ t, ∃ a, f a = g t := fun t => by
      obtain ⟨a, -, ha⟩ := hg t
      exact ⟨a, ha⟩
    exact ⟨⟨liftOfIsInclusionHom f hf g hg'⟩,
      congrArg ULift.up (liftOfIsInclusionHom_comp f hf g hg')⟩

end Atoms.Diagrammatic
