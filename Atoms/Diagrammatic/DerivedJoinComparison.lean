import Atoms.Diagrammatic.SimplicialJoin
import Atoms.Diagrammatic.Joyal.Comparison
import Atoms.Diagrammatic.Joyal.JoinDualQuillen

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe u

namespace Atoms.Diagrammatic

noncomputable def derivedJoinComparison {X Y Z : DiagSet.{u}}
    (w : WithInitial.join X Y ⟶ Z) :
    SSet.join (DiagSet.toSSet.obj X) (DiagSet.toSSet.obj Y) ⟶ DiagSet.toSSet.obj Z :=
  sSetDiagSetAdj.homEquiv _ _
    ((toDiagSetJoinIso (DiagSet.toSSet.obj X) (DiagSet.toSSet.obj Y)).hom ≫
      WithInitial.joinMap (sSetDiagSetAdj.counit.app X) (sSetDiagSetAdj.counit.app Y) ≫ w)

private theorem comp_derivedJoinComparison {A X Y Z : DiagSet.{u}}
    (i : DiagSet.toSSet.obj A ⟶ SSet.join (DiagSet.toSSet.obj X) (DiagSet.toSSet.obj Y))
    (j : A ⟶ WithInitial.join X Y) (w : WithInitial.join X Y ⟶ Z)
    (hi : SSet.toDiagSet.map i ≫
        (toDiagSetJoinIso (DiagSet.toSSet.obj X) (DiagSet.toSSet.obj Y)).hom ≫
          WithInitial.joinMap (sSetDiagSetAdj.counit.app X) (sSetDiagSetAdj.counit.app Y) =
        sSetDiagSetAdj.counit.app A ≫ j) :
    i ≫ derivedJoinComparison w = DiagSet.toSSet.map (j ≫ w) := by
  rw [derivedJoinComparison, ← sSetDiagSetAdj.homEquiv_naturality_left]
  simp only [← Category.assoc] at hi ⊢
  rw [hi, Category.assoc, sSetDiagSetAdj.homEquiv_naturality_right]
  simp [Adjunction.homEquiv_unit]

@[reassoc] theorem joinInclLeft_comp_derivedJoinComparison {X Y Z : DiagSet.{u}}
    (w : WithInitial.join X Y ⟶ Z) :
    SSet.joinInclLeft _ _ ≫ derivedJoinComparison w =
      DiagSet.toSSet.map (WithInitial.joinInclLeft X Y ≫ w) :=
  comp_derivedJoinComparison _ _ w
    ((Category.assoc _ _ _).symm.trans
      ((toDiagSet_map_joinInclLeft_comp_toDiagSetJoinIso_hom _ _ =≫ _).trans
        (WithInitial.joinInclLeft_comp_joinMap _ _)))

@[reassoc] theorem joinInclRight_comp_derivedJoinComparison {X Y Z : DiagSet.{u}}
    (w : WithInitial.join X Y ⟶ Z) :
    SSet.joinInclRight _ _ ≫ derivedJoinComparison w =
      DiagSet.toSSet.map (WithInitial.joinInclRight X Y ≫ w) :=
  comp_derivedJoinComparison _ _ w
    ((Category.assoc _ _ _).symm.trans
      ((toDiagSet_map_joinInclRight_comp_toDiagSetJoinIso_hom _ _ =≫ _).trans
        (WithInitial.joinInclRight_comp_joinMap _ _)))

@[reassoc] theorem derivedJoinComparison_naturality
    {X X' Y Y' Z Z' : DiagSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    (w : WithInitial.join X Y ⟶ Z) (w' : WithInitial.join X' Y' ⟶ Z')
    (h : Z ⟶ Z') (comm : WithInitial.joinMap f g ≫ w' = w ≫ h) :
    SSet.joinMap (DiagSet.toSSet.map f) (DiagSet.toSSet.map g) ≫ derivedJoinComparison w' =
      derivedJoinComparison w ≫ DiagSet.toSSet.map h := by
  have ef : SSet.toDiagSet.map (DiagSet.toSSet.map f) ≫ sSetDiagSetAdj.counit.app X' =
      sSetDiagSetAdj.counit.app X ≫ f := sSetDiagSetAdj.counit.naturality f
  have eg : SSet.toDiagSet.map (DiagSet.toSSet.map g) ≫ sSetDiagSetAdj.counit.app Y' =
      sSetDiagSetAdj.counit.app Y ≫ g := sSetDiagSetAdj.counit.naturality g
  apply sSetDiagSetAdj.homEquiv_naturality_left_square
  rw [← Category.assoc, ← Category.assoc,
    toDiagSet_map_joinMap_comp_toDiagSetJoinIso_hom]
  simp only [Category.assoc]
  rw [← Category.assoc (WithInitial.joinMap _ _) (WithInitial.joinMap _ _) w',
    WithInitial.joinMap_comp_joinMap,
    ef, eg,
    ← WithInitial.joinMap_comp_joinMap, Category.assoc, comm]

@[reassoc] theorem derivedJoinComparison_comp {X Y Z Z' : DiagSet.{u}}
    (w : WithInitial.join X Y ⟶ Z) (h : Z ⟶ Z') :
    derivedJoinComparison (w ≫ h) = derivedJoinComparison w ≫ DiagSet.toSSet.map h := by
  simp only [derivedJoinComparison, ← sSetDiagSetAdj.homEquiv_naturality_right, Category.assoc]

theorem exists_fibrant_join_replacement (X Y : DiagSet.{u}) :
    ∃ (Z : DiagSet.{u}) (w : WithInitial.join X Y ⟶ Z),
      IsInftyCategory 1 Z ∧ Cofibration ((DiagSet.toInfty 1).map w) ∧
        WeakEquivalence ((DiagSet.toInfty 1).map w) := by
  let A := (DiagSet.toInfty 1).obj (WithInitial.join X Y)
  let ψ := factorizationData (trivialCofibrations (DiagSet.Infty.{u} 1)) (fibrations _)
    (terminal.from A)
  have hZ : IsFibrant ψ.Z := by
    rw [isFibrant_iff, Subsingleton.elim (terminal.from ψ.Z) ψ.p]
    exact (fibration_iff _).2 ψ.hp
  exact ⟨ψ.Z, ψ.i, (isFibrant_infty_iff 1 _).1 hZ,
    (cofibration_iff _).2 ψ.hi.1, (weakEquivalence_iff _).2 ψ.hi.2⟩

theorem exists_derivedJoinComparison_naturality {X X' Y Y' Z Z' : DiagSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y')
    (w : WithInitial.join X Y ⟶ Z) (w' : WithInitial.join X' Y' ⟶ Z')
    (hw : Cofibration ((DiagSet.toInfty 1).map w))
    (ew : WeakEquivalence ((DiagSet.toInfty 1).map w)) (hZ' : IsInftyCategory 1 Z') :
    ∃ h : Z ⟶ Z', WithInitial.joinMap f g ≫ w' = w ≫ h ∧
      SSet.joinMap (DiagSet.toSSet.map f) (DiagSet.toSSet.map g) ≫ derivedJoinComparison w' =
        derivedJoinComparison w ≫ DiagSet.toSSet.map h := by
  have : IsFibrant ((DiagSet.toInfty 1).obj Z') := (isFibrant_infty_iff 1 _).2 hZ'
  have : Cofibration ((DiagSet.toInfty 1).map w) := hw
  have : WeakEquivalence ((DiagSet.toInfty 1).map w) := ew
  let sq : CommSq ((DiagSet.toInfty 1).map (WithInitial.joinMap f g ≫ w'))
      ((DiagSet.toInfty 1).map w) (terminal.from ((DiagSet.toInfty 1).obj Z'))
      (terminal.from ((DiagSet.toInfty 1).obj Z)) := ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left.symm,
    derivedJoinComparison_naturality f g w w' sq.lift sq.fac_left.symm⟩

open SSet.modelCategoryJoyal in
theorem exists_weakEquivalence_join_replacement_comparison {X Y Z Z' : DiagSet.{u}}
    (w : WithInitial.join X Y ⟶ Z) (w' : WithInitial.join X Y ⟶ Z')
    (hw : Cofibration ((DiagSet.toInfty 1).map w))
    (ew : WeakEquivalence ((DiagSet.toInfty 1).map w))
    (ew' : WeakEquivalence ((DiagSet.toInfty 1).map w'))
    (hZ : IsInftyCategory 1 Z) (hZ' : IsInftyCategory 1 Z') :
    ∃ h : Z ⟶ Z', w ≫ h = w' ∧ WeakEquivalence ((DiagSet.toInfty 1).map h) ∧
      WeakEquivalence (DiagSet.toSSet.map h) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj Z) := (isFibrant_infty_iff 1 _).2 hZ
  have : IsFibrant ((DiagSet.toInfty 1).obj Z') := (isFibrant_infty_iff 1 _).2 hZ'
  have : WeakEquivalence ((DiagSet.toInfty 1).map w) := ew
  obtain ⟨h, comm, -⟩ := exists_derivedJoinComparison_naturality (𝟙 X) (𝟙 Y) w w' hw ew hZ'
  have wh : w ≫ h = w' := by
    simpa only [WithInitial.joinMap_id, Category.id_comp] using comm.symm
  have : WeakEquivalence ((DiagSet.toInfty 1).map w ≫ (DiagSet.toInfty 1).map h) :=
    wh.symm ▸ ew'
  have eh : WeakEquivalence ((DiagSet.toInfty 1).map h) :=
    weakEquivalence_of_precomp ((DiagSet.toInfty 1).map w) ((DiagSet.toInfty 1).map h)
  have eRh : WeakEquivalence (DiagSet.toSSet.map h) :=
    isQuillen_sSetDiagSetAdj.weakEquivalence_map_of_isFibrant ((DiagSet.toInfty 1).map h)
  exact ⟨h, wh, eh, eRh⟩

open SSet.modelCategoryJoyal in
theorem exists_iso_derivedJoinComparison {X Y Z Z' : DiagSet.{u}}
    (w : WithInitial.join X Y ⟶ Z) (w' : WithInitial.join X Y ⟶ Z')
    (ew : WeakEquivalence ((DiagSet.toInfty 1).map w))
    (ew' : WeakEquivalence ((DiagSet.toInfty 1).map w'))
    (hZ : IsInftyCategory 1 Z) (hZ' : IsInftyCategory 1 Z') :
    ∃ e : (weakEquivalences SSet.{u}).Q.obj (DiagSet.toSSet.obj Z) ≅
        (weakEquivalences SSet.{u}).Q.obj (DiagSet.toSSet.obj Z'),
      (weakEquivalences SSet.{u}).Q.map (derivedJoinComparison w) ≫ e.hom =
        (weakEquivalences SSet.{u}).Q.map (derivedJoinComparison w') := by
  obtain ⟨F, i, hF, hi, ei⟩ := exists_fibrant_join_replacement X Y
  obtain ⟨h, ih, eh, eRh⟩ :=
    exists_weakEquivalence_join_replacement_comparison i w hi ei ew hF hZ
  obtain ⟨h', ih', eh', eRh'⟩ :=
    exists_weakEquivalence_join_replacement_comparison i w' hi ei ew' hF hZ'
  let Q := (weakEquivalences SSet.{u}).Q
  let e := Localization.isoOfHom Q (weakEquivalences SSet.{u})
    (DiagSet.toSSet.map h) ((weakEquivalence_iff _).1 eRh)
  let e' := Localization.isoOfHom Q (weakEquivalences SSet.{u})
    (DiagSet.toSSet.map h') ((weakEquivalence_iff _).1 eRh')
  refine ⟨e.symm ≪≫ e', ?_⟩
  have c : Q.map (derivedJoinComparison i) ≫ e.hom = Q.map (derivedJoinComparison w) := by
    simpa only [e, Localization.isoOfHom_hom, derivedJoinComparison_comp, Functor.map_comp] using
      congrArg (fun k ↦ Q.map (derivedJoinComparison k)) ih
  have c' : Q.map (derivedJoinComparison i) ≫ e'.hom = Q.map (derivedJoinComparison w') := by
    simpa only [e', Localization.isoOfHom_hom, derivedJoinComparison_comp, Functor.map_comp] using
      congrArg (fun k ↦ Q.map (derivedJoinComparison k)) ih'
  change Q.map (derivedJoinComparison w) ≫ e.inv ≫ e'.hom = _
  rw [← c, Category.assoc, e.hom_inv_id_assoc, c']

theorem weakEquivalence_joinMap_counit_app_id
    (hinvL : ∀ (T : DiagSet.{u}) {A B : DiagSet.{u}} (f : A ⟶ B),
      WeakEquivalence ((DiagSet.toInfty 1).map f) →
        WeakEquivalence ((DiagSet.toInfty 1).map (WithInitial.joinMap f (𝟙 T))))
    {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) (T : DiagSet.{u}) :
    WeakEquivalence ((DiagSet.toInfty 1).map
      (WithInitial.joinMap (sSetDiagSetAdj.counit.app X) (𝟙 T))) :=
  hinvL T (sSetDiagSetAdj.counit.app X) (weakEquivalence_sSetDiagSetAdj_counit_app
    ((DiagSet.toInfty 1).obj X) ((isFibrant_infty_iff 1 _).2 hX))

theorem weakEquivalence_joinMap_id_counit_app
    (hinvR : ∀ (T : DiagSet.{u}) {A B : DiagSet.{u}} (g : A ⟶ B),
      WeakEquivalence ((DiagSet.toInfty 1).map g) →
        WeakEquivalence ((DiagSet.toInfty 1).map (WithInitial.joinMap (𝟙 T) g)))
    (T : DiagSet.{u}) {Y : DiagSet.{u}} (hY : IsInftyCategory 1 Y) :
    WeakEquivalence ((DiagSet.toInfty 1).map
      (WithInitial.joinMap (𝟙 T) (sSetDiagSetAdj.counit.app Y))) :=
  hinvR T (sSetDiagSetAdj.counit.app Y) (weakEquivalence_sSetDiagSetAdj_counit_app
    ((DiagSet.toInfty 1).obj Y) ((isFibrant_infty_iff 1 _).2 hY))

theorem weakEquivalence_joinMap_counit_app
    (hinvL : ∀ (T : DiagSet.{u}) {A B : DiagSet.{u}} (f : A ⟶ B),
      WeakEquivalence ((DiagSet.toInfty 1).map f) →
        WeakEquivalence ((DiagSet.toInfty 1).map (WithInitial.joinMap f (𝟙 T))))
    (hinvR : ∀ (T : DiagSet.{u}) {A B : DiagSet.{u}} (g : A ⟶ B),
      WeakEquivalence ((DiagSet.toInfty 1).map g) →
        WeakEquivalence ((DiagSet.toInfty 1).map (WithInitial.joinMap (𝟙 T) g)))
    {X Y : DiagSet.{u}} (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) :
    WeakEquivalence ((DiagSet.toInfty 1).map
      (WithInitial.joinMap (sSetDiagSetAdj.counit.app X) (sSetDiagSetAdj.counit.app Y))) := by
  have e : WithInitial.joinMap (sSetDiagSetAdj.counit.app X) (sSetDiagSetAdj.counit.app Y) =
      WithInitial.joinMap (sSetDiagSetAdj.counit.app X)
          (𝟙 (SSet.toDiagSet.obj (DiagSet.toSSet.obj Y))) ≫
        WithInitial.joinMap (𝟙 X) (sSetDiagSetAdj.counit.app Y) := by
    rw [WithInitial.joinMap_comp_joinMap]
    simp only [Functor.id_obj, Functor.comp_obj, Category.comp_id, Category.id_comp]
  have h₁ := weakEquivalence_joinMap_counit_app_id hinvL hX
    (SSet.toDiagSet.obj (DiagSet.toSSet.obj Y))
  have h₂ := weakEquivalence_joinMap_id_counit_app hinvR X hY
  rw [e, Functor.map_comp]
  infer_instance

open SSet.modelCategoryJoyal in
theorem weakEquivalence_derivedJoinComparison_of_joinInvariance
    (hinvL : ∀ (T : DiagSet.{u}) {A B : DiagSet.{u}} (f : A ⟶ B),
      WeakEquivalence ((DiagSet.toInfty 1).map f) →
        WeakEquivalence ((DiagSet.toInfty 1).map (WithInitial.joinMap f (𝟙 T))))
    (hinvR : ∀ (T : DiagSet.{u}) {A B : DiagSet.{u}} (g : A ⟶ B),
      WeakEquivalence ((DiagSet.toInfty 1).map g) →
        WeakEquivalence ((DiagSet.toInfty 1).map (WithInitial.joinMap (𝟙 T) g)))
    {X Y Z : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (hZ : IsInftyCategory 1 Z) (w : WithInitial.join X Y ⟶ Z)
    (hw : WeakEquivalence ((DiagSet.toInfty 1).map w)) :
    WeakEquivalence (sSetDiagSetAdj.homEquiv _ _
      ((toDiagSetJoinIso (DiagSet.toSSet.obj X) (DiagSet.toSSet.obj Y)).hom ≫
        WithInitial.joinMap (sSetDiagSetAdj.counit.app X)
          (sSetDiagSetAdj.counit.app Y) ≫ w)) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj Z) := (isFibrant_infty_iff 1 _).2 hZ
  have : IsCofibrant (SSet.join (DiagSet.toSSet.obj X) (DiagSet.toSSet.obj Y)) := by
    rw [isCofibrant_iff, cofibration_iff]
    exact monomorphisms.infer_property _
  have := weakEquivalence_joinMap_counit_app hinvL hinvR hX hY
  have : WeakEquivalence ((DiagSet.toInfty 1).map
      (toDiagSetJoinIso (DiagSet.toSSet.obj X) (DiagSet.toSSet.obj Y)).hom) := inferInstance
  have h : WeakEquivalence ((DiagSet.toInfty 1).map
      ((toDiagSetJoinIso (DiagSet.toSSet.obj X) (DiagSet.toSSet.obj Y)).hom ≫
        WithInitial.joinMap (sSetDiagSetAdj.counit.app X)
          (sSetDiagSetAdj.counit.app Y) ≫ w)) := by
    simp only [Functor.map_comp]
    infer_instance
  exact (isQuillenEquivalence_sSetDiagSetAdj.weakEquivalence_iff
    (A := SSet.join (DiagSet.toSSet.obj X) (DiagSet.toSSet.obj Y))
    (X := (DiagSet.toInfty 1).obj Z) _).1 h

open SSet.modelCategoryJoyal in
theorem weakEquivalence_derivedJoinComparison {X Y Z : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (hZ : IsInftyCategory 1 Z) (w : WithInitial.join X Y ⟶ Z)
    (hw : WeakEquivalence ((DiagSet.toInfty 1).map w)) :
    WeakEquivalence (sSetDiagSetAdj.homEquiv _ _
      ((toDiagSetJoinIso (DiagSet.toSSet.obj X) (DiagSet.toSSet.obj Y)).hom ≫
        WithInitial.joinMap (sSetDiagSetAdj.counit.app X)
          (sSetDiagSetAdj.counit.app Y) ≫ w)) :=
  weakEquivalence_derivedJoinComparison_of_joinInvariance
    (fun T _ _ f hf ↦ weakEquivalence_joinMap_id f T (hf := hf))
    (fun T _ _ g hg ↦ weakEquivalence_joinMap_id_left T g (hg := hg)) hX hY hZ w hw

end Atoms.Diagrammatic
