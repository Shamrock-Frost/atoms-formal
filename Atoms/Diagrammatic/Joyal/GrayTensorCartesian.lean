import Atoms.Diagrammatic.GrayTensorProduct
import Atoms.Diagrammatic.Joyal.GrayTensorModel
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Product
import Atoms.Homotopical.Simplicial.CartesianMonoidal

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra MonoidalCategory
open Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open MarkedSSet.modelCategoryCartesian SSet.modelCategoryJoyal

private theorem weakEquivalence_markedSSet_prodMap {A A' B B' : MarkedSSet.{u}} (f : A ⟶ A')
    (g : B ⟶ B') [WeakEquivalence f] [WeakEquivalence g] : WeakEquivalence (prod.map f g) := by
  have hl {Z B B' : MarkedSSet.{u}} (g : B ⟶ B') [WeakEquivalence g] :
      WeakEquivalence (prod.map (𝟙 Z) g) := by
    have := MarkedSSet.weakEquivalence_whiskerLeft Z g
    have h : WeakEquivalence ((CartesianMonoidalCategory.tensorLeftIsoProd Z).inv.app B ≫
        (MonoidalCategory.tensorLeft Z).map g ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd Z).hom.app B') :=
      (weakEquivalence_iff _).2 ((weakEquivalences _).comp_mem _ _
        ((weakEquivalences _).of_isIso _) ((weakEquivalences _).comp_mem _ _
          ((weakEquivalence_iff _).1 this) ((weakEquivalences _).of_isIso _)))
    rw [NatIso.naturality_1] at h
    exact h
  have := hl (Z := A') g
  have := hl (Z := B) f
  have : WeakEquivalence (prod.map f (𝟙 B) ≫ (prod.braiding A' B).hom) := by
    rw [braid_natural]
    infer_instance
  have := weakEquivalence_of_postcomp (prod.map f (𝟙 B)) (prod.braiding A' B).hom
  have e : prod.map f g = prod.map f (𝟙 B) ≫ prod.map (𝟙 A') g := by
    rw [prod.map_map, Category.comp_id, Category.id_comp]
  rw [e]
  infer_instance

private theorem weakEquivalence_prodComparison_flat_markedFaceNerve
    (X Y : DiagSet.Infty.{u} 1) [IsFibrant X] [IsFibrant Y] :
    WeakEquivalence (prodComparison
      (DiagSet.Infty.flat.{u} 1 ⋙ MarkedDiagSet.Coinductive.markedFaceNerve) X Y) := by
  let L := DiagSet.Infty.flat.{u} 1 ⋙ MarkedDiagSet.Coinductive.markedFaceNerve
  let adj : L ⊣ _ := faceNerveAdjunction.{u}
  have hq := isQuillenEquivalence_faceNerveAdjunction.{u}
  let ψX := factorizationData (trivialCofibrations MarkedSSet.{u}) (fibrations _)
    (terminal.from (L.obj X))
  let ψY := factorizationData (trivialCofibrations MarkedSSet.{u}) (fibrations _)
    (terminal.from (L.obj Y))
  have : IsFibrant ψX.Z := by
    rw [HomotopicalAlgebra.isFibrant_iff, Subsingleton.elim (terminal.from ψX.Z) ψX.p]
    infer_instance
  have : IsFibrant ψY.Z := by
    rw [HomotopicalAlgebra.isFibrant_iff, Subsingleton.elim (terminal.from ψY.Z) ψY.p]
    infer_instance
  have : WeakEquivalence ψX.i := (weakEquivalence_iff _).2 ψX.hi.2
  have : WeakEquivalence ψY.i := (weakEquivalence_iff _).2 ψY.hi.2
  have : IsFibrant (ψX.Z ⨯ ψY.Z) := isFibrant_of_fibration (prod.fst : ψX.Z ⨯ ψY.Z ⟶ ψX.Z)
  have := weakEquivalence_markedSSet_prodMap ψX.i ψY.i
  let aX := adj.homEquiv X ψX.Z ψX.i
  let aY := adj.homEquiv Y ψY.Z ψY.i
  have : WeakEquivalence aX := (hq.weakEquivalence_iff ψX.i).1 inferInstance
  have : WeakEquivalence aY := (hq.weakEquivalence_iff ψY.i).1 inferInstance
  have := isQuillen_faceNerveAdjunction.{u}.isFibrant_obj ψX.Z
  have := isQuillen_faceNerveAdjunction.{u}.isFibrant_obj ψY.Z
  have := weakEquivalence_prodMap aX aY
  let f := prodComparison L X Y ≫ prod.map ψX.i ψY.i
  have := adj.rightAdjoint_preservesLimits
  have e : adj.homEquiv _ _ f ≫ prodComparison _ ψX.Z ψY.Z = prod.map aX aY := by
    ext
    · rw [Category.assoc, prodComparison_fst, ← adj.homEquiv_naturality_right, prod.map_fst]
      simp only [f, Category.assoc, prod.map_fst, prodComparison_fst_assoc]
      exact adj.homEquiv_naturality_left _ _
    · rw [Category.assoc, prodComparison_snd, ← adj.homEquiv_naturality_right, prod.map_snd]
      simp only [f, Category.assoc, prod.map_snd, prodComparison_snd_assoc]
      exact adj.homEquiv_naturality_left _ _
  have : WeakEquivalence (adj.homEquiv _ _ f ≫ prodComparison _ ψX.Z ψY.Z) := e ▸ inferInstance
  have := weakEquivalence_of_postcomp (adj.homEquiv _ _ f) (prodComparison _ ψX.Z ψY.Z)
  have : WeakEquivalence f := (hq.weakEquivalence_iff f).2 this
  exact weakEquivalence_of_postcomp _ (prod.map ψX.i ψY.i)

theorem weakEquivalence_prodComparison_faceNerve {X Y : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) :
    WeakEquivalence (prodComparison faceNerve X Y) :=
  have : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 _).2 hX
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  weakEquivalence_prodComparison_flat_markedFaceNerve ((DiagSet.toInfty 1).obj X)
    ((DiagSet.toInfty 1).obj Y)

private theorem faceNerve_map_grayTensorToProd_comp_prodComparison (X Y : DiagSet.{u}) :
    faceNerve.map (grayTensorToProd X Y) ≫ prodComparison faceNerve X Y =
      faceNerveGrayTensorIso.hom.app (X, Y) := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, prodComparison_fst, ← Functor.map_comp, grayTensorToProd, prod.lift_fst]
    exact (faceNerveGrayTensorIso_hom_app_fst X Y).symm
  · rw [Category.assoc, prodComparison_snd, ← Functor.map_comp, grayTensorToProd, prod.lift_snd]
    exact (faceNerveGrayTensorIso_hom_app_snd X Y).symm

theorem weakEquivalence_toInfty_one_grayTensorToProd {X Y : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) :
    WeakEquivalence ((DiagSet.toInfty 1).map (grayTensorToProd X Y)) := by
  have := weakEquivalence_prodComparison_faceNerve hX hY
  have : IsIso (faceNerve.map (grayTensorToProd X Y) ≫ prodComparison faceNerve X Y) :=
    (faceNerve_map_grayTensorToProd_comp_prodComparison X Y).symm ▸
      (faceNerveGrayTensorIso.app (X, Y)).isIso_hom
  have : WeakEquivalence (faceNerve.map (grayTensorToProd X Y) ≫ prodComparison faceNerve X Y) :=
    (weakEquivalence_iff _).2 ((weakEquivalences _).of_isIso _)
  have := weakEquivalence_of_postcomp (faceNerve.map (grayTensorToProd X Y))
    (prodComparison faceNerve X Y)
  exact ((isQuillen_faceNerveAdjunction.isQuillenEquivalence_iff_of_isCofibrant).1
    isQuillenEquivalence_faceNerveAdjunction).1 _ this

theorem weakEquivalence_toInfty_one_grayTensorBifunctor_map_comp_grayTensorToProd
    {A A' B B' : DiagSet.{u}} (a : A ⟶ A') (b : B ⟶ B')
    (ha : WeakEquivalence ((DiagSet.toInfty 1).map a))
    (hb : WeakEquivalence ((DiagSet.toInfty 1).map b))
    (hA' : IsInftyCategory 1 A') (hB' : IsInftyCategory 1 B') :
    WeakEquivalence ((DiagSet.toInfty 1).map
      (grayTensorBifunctor.map ((a, b) : (A, B) ⟶ (A', B')) ≫ grayTensorToProd A' B')) := by
  have e : grayTensorBifunctor.map ((a, b) : (A, B) ⟶ (A', B')) =
      grayTensorBifunctor.map ((a, 𝟙 B) : (A, B) ⟶ (A', B)) ≫
        grayTensorBifunctor.map ((𝟙 A', b) : (A', B) ⟶ (A', B')) := by
    rw [← Functor.map_comp, prod_comp, Category.comp_id, Category.id_comp]
  have : WeakEquivalence ((DiagSet.toInfty 1).map
      (grayTensorBifunctor.map ((a, 𝟙 B) : (A, B) ⟶ (A', B)))) :=
    DiagSet.Infty.weakEquivalence_toInfty_one_grayTensorRight_map B a ha
  have : WeakEquivalence ((DiagSet.toInfty 1).map
      (grayTensorBifunctor.map ((𝟙 A', b) : (A', B) ⟶ (A', B')))) :=
    DiagSet.Infty.weakEquivalence_toInfty_one_grayTensorLeft_map A' b hb
  have := weakEquivalence_toInfty_one_grayTensorToProd hA' hB'
  rw [e, Functor.map_comp, Functor.map_comp]
  infer_instance

theorem weakEquivalence_toSSet_map_comp_prodComparison
    {A T X Y : DiagSet.{u}} (hT : IsInftyCategory 1 T)
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (r : A ⟶ T) (q : T ⟶ X ⨯ Y)
    (hr : WeakEquivalence ((DiagSet.toInfty 1).map r))
    (hc : WeakEquivalence ((DiagSet.toInfty 1).map (r ≫ q))) :
    WeakEquivalence (DiagSet.toSSet.map q ≫ prodComparison DiagSet.toSSet X Y) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj T) := (isFibrant_infty_iff 1 _).2 hT
  have : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 _).2 hX
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have : IsFibrant (((DiagSet.toInfty 1).obj X) ⨯ ((DiagSet.toInfty 1).obj Y)) :=
    isFibrant_of_fibration (prod.fst :
      ((DiagSet.toInfty 1).obj X) ⨯ ((DiagSet.toInfty 1).obj Y) ⟶ (DiagSet.toInfty 1).obj X)
  have : PreservesLimits (DiagSet.toInfty 1) :=
    inferInstanceAs (PreservesLimits (𝟭 DiagSet.{u}))
  have : Fibration (prodComparison (DiagSet.toInfty 1) X Y) :=
    (fibration_iff _).2 ((fibrations _).of_isIso _)
  have : IsFibrant ((DiagSet.toInfty 1).obj (X ⨯ Y)) :=
    isFibrant_of_fibration (prodComparison (DiagSet.toInfty 1) X Y)
  have : WeakEquivalence ((DiagSet.toInfty 1).map q) := by
    have : WeakEquivalence ((DiagSet.toInfty 1).map r ≫ (DiagSet.toInfty 1).map q) := by
      rwa [← Functor.map_comp]
    exact weakEquivalence_of_precomp ((DiagSet.toInfty 1).map r) _
  have : WeakEquivalence (DiagSet.toSSet.map q) :=
    isQuillen_sSetDiagSetAdj.weakEquivalence_map_of_isFibrant
    ((DiagSet.toInfty 1).map q)
  have := sSetDiagSetAdj.rightAdjoint_preservesLimits
  have : WeakEquivalence (prodComparison DiagSet.toSSet X Y) :=
    (weakEquivalence_iff _).2 ((weakEquivalences _).of_isIso _)
  infer_instance

theorem exists_fibrant_extension_toSSet_prodComparison
    {A X Y : DiagSet.{u}} (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (c : A ⟶ X ⨯ Y) (hc : WeakEquivalence ((DiagSet.toInfty 1).map c)) :
    ∃ T : DiagSet.{u}, IsInftyCategory 1 T ∧
      ∃ (r : A ⟶ T) (q : T ⟶ X ⨯ Y),
        Mono r ∧ WeakEquivalence ((DiagSet.toInfty 1).map r) ∧ r ≫ q = c ∧
        WeakEquivalence (DiagSet.toSSet.map q ≫ prodComparison DiagSet.toSSet X Y) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 _).2 hX
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have : IsFibrant (((DiagSet.toInfty 1).obj X) ⨯ ((DiagSet.toInfty 1).obj Y)) :=
    isFibrant_of_fibration (prod.fst : _ ⟶ (DiagSet.toInfty 1).obj X)
  let φ := factorizationData (trivialCofibrations (DiagSet.Infty.{u} 1)) (fibrations _)
    (terminal.from ((DiagSet.toInfty 1).obj A))
  have : IsFibrant φ.Z := by
    rw [HomotopicalAlgebra.isFibrant_iff, Subsingleton.elim (terminal.from φ.Z) φ.p]
    infer_instance
  have hr : WeakEquivalence φ.i := (weakEquivalence_iff _).2 φ.hi.2
  have hT := (isFibrant_infty_iff 1 φ.Z).1 inferInstance
  have : Cofibration φ.i := (cofibration_iff _).2 φ.hi.1
  let c' : (DiagSet.toInfty 1).obj A ⟶
      ((DiagSet.toInfty 1).obj X) ⨯ ((DiagSet.toInfty 1).obj Y) := c
  let sq : CommSq c' φ.i
      (terminal.from (((DiagSet.toInfty 1).obj X) ⨯ ((DiagSet.toInfty 1).obj Y)))
      (terminal.from φ.Z) := ⟨terminal.hom_ext _ _⟩
  refine ⟨φ.Z, hT, φ.i, sq.lift, φ.hi.1, hr, sq.fac_left, ?_⟩
  exact weakEquivalence_toSSet_map_comp_prodComparison hT hX hY φ.i sq.lift hr
    (sq.fac_left.symm ▸ hc)

theorem derivedGrayTensorComparison_exists {X Y : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) :
    ∃ T : DiagSet.{u}, IsInftyCategory 1 T ∧
      ∃ (r : grayTensor X Y ⟶ T) (q : T ⟶ X ⨯ Y),
        Mono r ∧ WeakEquivalence ((DiagSet.toInfty 1).map r) ∧
        r ≫ q = grayTensorToProd X Y ∧
        WeakEquivalence (DiagSet.toSSet.map q ≫ prodComparison DiagSet.toSSet X Y) :=
  exists_fibrant_extension_toSSet_prodComparison hX hY (grayTensorToProd X Y)
    (weakEquivalence_toInfty_one_grayTensorToProd hX hY)

theorem derivedGrayTensorComparison_replacements_exists
    {A B X Y : DiagSet.{u}} (a : A ⟶ X) (b : B ⟶ Y)
    (ha : WeakEquivalence ((DiagSet.toInfty 1).map a))
    (hb : WeakEquivalence ((DiagSet.toInfty 1).map b))
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) :
    ∃ T : DiagSet.{u}, IsInftyCategory 1 T ∧
      ∃ (r : grayTensor A B ⟶ T) (q : T ⟶ X ⨯ Y),
        Mono r ∧ WeakEquivalence ((DiagSet.toInfty 1).map r) ∧
        r ≫ q = grayTensorBifunctor.map (a, b) ≫ grayTensorToProd X Y ∧
        WeakEquivalence (DiagSet.toSSet.map q ≫ prodComparison DiagSet.toSSet X Y) :=
  exists_fibrant_extension_toSSet_prodComparison hX hY _
    (weakEquivalence_toInfty_one_grayTensorBifunctor_map_comp_grayTensorToProd
      a b ha hb hX hY)

noncomputable def derivedGrayTensorComparisonIso {H : Type*} [Category* H]
    (L : SSet.{u} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{u})]
    {T X Y : DiagSet.{u}} (q : T ⟶ X ⨯ Y)
    [WeakEquivalence (DiagSet.toSSet.map q ≫ prodComparison DiagSet.toSSet X Y)] :
    L.obj (DiagSet.toSSet.obj T) ≅
      L.obj (DiagSet.toSSet.obj X ⨯ DiagSet.toSSet.obj Y) :=
  Localization.isoOfHom L (weakEquivalences _)
    (DiagSet.toSSet.map q ≫ prodComparison DiagSet.toSSet X Y)
    ((weakEquivalence_iff _).1 inferInstance)

theorem derivedGrayTensorComparisonIso_map {H : Type*} [Category* H]
    (L : SSet.{u} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{u})]
    {T T' X Y X' Y' : DiagSet.{u}} (q : T ⟶ X ⨯ Y) (q' : T' ⟶ X' ⨯ Y')
    [WeakEquivalence (DiagSet.toSSet.map q ≫ prodComparison DiagSet.toSSet X Y)]
    [WeakEquivalence (DiagSet.toSSet.map q' ≫ prodComparison DiagSet.toSSet X' Y')]
    (t : T ⟶ T') (f : X ⟶ X') (g : Y ⟶ Y')
    (ht : t ≫ q' = q ≫ prod.map f g) :
    L.map (DiagSet.toSSet.map t) =
      (derivedGrayTensorComparisonIso L q).hom ≫
        L.map (prod.map (DiagSet.toSSet.map f) (DiagSet.toSSet.map g)) ≫
        (derivedGrayTensorComparisonIso L q').inv := by
  apply (cancel_mono (derivedGrayTensorComparisonIso L q').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change L.map (DiagSet.toSSet.map t) ≫
      L.map (DiagSet.toSSet.map q' ≫ prodComparison DiagSet.toSSet X' Y') =
    L.map (DiagSet.toSSet.map q ≫ prodComparison DiagSet.toSSet X Y) ≫ _
  rw [← L.map_comp, ← L.map_comp]
  congr 1
  rw [← Functor.map_comp_assoc, ht, Functor.map_comp, Category.assoc,
    prodComparison_natural, Category.assoc]

theorem map_derivedGrayTensorComparison_naturality {H : Type*} [Category* H]
    (L : DiagSet.Infty.{u} 1 ⥤ H)
    [L.IsLocalization (weakEquivalences (DiagSet.Infty.{u} 1))]
    {X Y X' Y' T T' : DiagSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    (r : grayTensor X Y ⟶ T) (r' : grayTensor X' Y' ⟶ T')
    (q : T ⟶ X ⨯ Y) (q' : T' ⟶ X' ⨯ Y') (t : T ⟶ T')
    (hr : WeakEquivalence ((DiagSet.toInfty 1).map r))
    (hq : r ≫ q = grayTensorToProd X Y)
    (hq' : r' ≫ q' = grayTensorToProd X' Y')
    (ht : r ≫ t = grayTensorBifunctor.map (f, g) ≫ r') :
    L.map ((DiagSet.toInfty 1).map t) ≫ L.map ((DiagSet.toInfty 1).map q') =
      L.map ((DiagSet.toInfty 1).map q) ≫
        L.map ((DiagSet.toInfty 1).map (prod.map f g)) := by
  let hi := Localization.isoOfHom L (weakEquivalences _) ((DiagSet.toInfty 1).map r)
    ((weakEquivalence_iff _).1 hr)
  apply (cancel_epi hi.hom).1
  change L.map ((DiagSet.toInfty 1).map r) ≫
      L.map ((DiagSet.toInfty 1).map t) ≫ L.map ((DiagSet.toInfty 1).map q') =
    L.map ((DiagSet.toInfty 1).map r) ≫ L.map ((DiagSet.toInfty 1).map q) ≫
      L.map ((DiagSet.toInfty 1).map (prod.map f g))
  simp only [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc]
  congr 2
  rw [ht, Category.assoc, hq', hq]
  apply prod.hom_ext
  · simp only [Category.assoc, grayTensorToProd, prod.lift_fst, prod.lift_fst_assoc,
      prod.map_fst]
    exact grayTensorBifunctor_map_grayTensorFst f g
  · simp only [Category.assoc, grayTensorToProd, prod.lift_snd, prod.lift_snd_assoc,
      prod.map_snd]
    exact grayTensorBifunctor_map_grayTensorSnd f g

theorem isInftyCategory_prod {X Y : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) : IsInftyCategory 1 (X ⨯ Y) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 _).2 hX
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have : IsFibrant (((DiagSet.toInfty 1).obj X) ⨯ ((DiagSet.toInfty 1).obj Y)) :=
    isFibrant_of_fibration (prod.fst :
      ((DiagSet.toInfty 1).obj X) ⨯ ((DiagSet.toInfty 1).obj Y) ⟶ (DiagSet.toInfty 1).obj X)
  have : PreservesLimits (DiagSet.toInfty 1) :=
    inferInstanceAs (PreservesLimits (𝟭 DiagSet.{u}))
  have : Fibration (prodComparison (DiagSet.toInfty 1) X Y) :=
    (fibration_iff _).2 ((fibrations _).of_isIso _)
  have : IsFibrant ((DiagSet.toInfty 1).obj (X ⨯ Y)) :=
    isFibrant_of_fibration (prodComparison (DiagSet.toInfty 1) X Y)
  exact (isFibrant_infty_iff 1 _).1 this

theorem map_toSSet_map_eq_of_comp_eq {H : Type*} [Category* H]
    (L : SSet.{u} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{u})]
    {A T Z : DiagSet.{u}} (hZ : IsInftyCategory 1 Z) (r : A ⟶ T)
    (hr : WeakEquivalence ((DiagSet.toInfty 1).map r)) (u v : T ⟶ Z) (h : r ≫ u = r ≫ v) :
    L.map (DiagSet.toSSet.map u) = L.map (DiagSet.toSSet.map v) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj Z) := (isFibrant_infty_iff 1 _).2 hZ
  let u' : (DiagSet.toInfty 1).obj T ⟶ (DiagSet.toInfty 1).obj Z := u
  let v' : (DiagSet.toInfty 1).obj T ⟶ (DiagSet.toInfty 1).obj Z := v
  have hc : RightHomotopyRel u' v' := by
    rw [← RightHomotopyClass.mk_eq_mk_iff]
    apply (RightHomotopyClass.precomp_bijective_of_weakEquivalence
      ((DiagSet.toInfty 1).obj Z) ((DiagSet.toInfty 1).map r)).1
    simp only [RightHomotopyClass.precomp_mk]
    exact congrArg RightHomotopyClass.mk h
  have h2 := isQuillen_sSetDiagSetAdj.rightHomotopyRel_homEquiv
    (hc.precomp (DiagSet.Infty.sSetDiagSetAdj.counit.app ((DiagSet.toInfty 1).obj T)))
  have e (w : (DiagSet.toInfty 1).obj T ⟶ (DiagSet.toInfty 1).obj Z) :
      DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _
        (DiagSet.Infty.sSetDiagSetAdj.counit.app ((DiagSet.toInfty 1).obj T) ≫ w) =
      DiagSet.toSSet.map w := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      Adjunction.right_triangle_components, Category.id_comp]
    rfl
  rw [e, e] at h2
  exact (areEqualizedByLocalization_iff L (weakEquivalences SSet.{u}) _ _).1
    (RightHomotopyRel.factorsThroughLocalization SSet.{u} h2)

private theorem comp_eq_of_comp_eq_grayTensorBifunctor_map
    {X Y X' Y' T T' : DiagSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    (r : grayTensor X Y ⟶ T) (r' : grayTensor X' Y' ⟶ T')
    (q : T ⟶ X ⨯ Y) (q' : T' ⟶ X' ⨯ Y') (t : T ⟶ T')
    (hq : r ≫ q = grayTensorToProd X Y)
    (hq' : r' ≫ q' = grayTensorToProd X' Y')
    (ht : r ≫ t = grayTensorBifunctor.map (f, g) ≫ r') :
    r ≫ t ≫ q' = r ≫ q ≫ prod.map f g := by
  rw [← Category.assoc, ht, Category.assoc, hq', ← Category.assoc, hq]
  apply prod.hom_ext
  · simp only [Category.assoc, grayTensorToProd, prod.lift_fst, prod.lift_fst_assoc,
      prod.map_fst]
    exact grayTensorBifunctor_map_grayTensorFst f g
  · simp only [Category.assoc, grayTensorToProd, prod.lift_snd, prod.lift_snd_assoc,
      prod.map_snd]
    exact grayTensorBifunctor_map_grayTensorSnd f g

theorem map_toSSet_derivedGrayTensorComparison_naturality {H : Type*} [Category* H]
    (L : SSet.{u} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{u})]
    {X Y X' Y' T T' : DiagSet.{u}} (hX' : IsInftyCategory 1 X') (hY' : IsInftyCategory 1 Y')
    (f : X ⟶ X') (g : Y ⟶ Y')
    (r : grayTensor X Y ⟶ T) (r' : grayTensor X' Y' ⟶ T')
    (q : T ⟶ X ⨯ Y) (q' : T' ⟶ X' ⨯ Y') (t : T ⟶ T')
    (hr : WeakEquivalence ((DiagSet.toInfty 1).map r))
    (hq : r ≫ q = grayTensorToProd X Y)
    (hq' : r' ≫ q' = grayTensorToProd X' Y')
    (ht : r ≫ t = grayTensorBifunctor.map (f, g) ≫ r') :
    L.map (DiagSet.toSSet.map t) ≫
        L.map (DiagSet.toSSet.map q' ≫ prodComparison DiagSet.toSSet X' Y') =
      L.map (DiagSet.toSSet.map q ≫ prodComparison DiagSet.toSSet X Y) ≫
        L.map (prod.map (DiagSet.toSSet.map f) (DiagSet.toSSet.map g)) := by
  have h := map_toSSet_map_eq_of_comp_eq L (isInftyCategory_prod hX' hY') r hr _ _
    (comp_eq_of_comp_eq_grayTensorBifunctor_map f g r r' q q' t hq hq' ht)
  rw [← L.map_comp, ← L.map_comp, Category.assoc, ← prodComparison_natural, ← Category.assoc,
    ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, L.map_comp, L.map_comp, h]

theorem derivedGrayTensorComparisonIso_map_of_comp_eq {H : Type*} [Category* H]
    (L : SSet.{u} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{u})]
    {X Y X' Y' T T' : DiagSet.{u}} (hX' : IsInftyCategory 1 X') (hY' : IsInftyCategory 1 Y')
    (f : X ⟶ X') (g : Y ⟶ Y')
    (r : grayTensor X Y ⟶ T) (r' : grayTensor X' Y' ⟶ T')
    (q : T ⟶ X ⨯ Y) (q' : T' ⟶ X' ⨯ Y') (t : T ⟶ T')
    [WeakEquivalence (DiagSet.toSSet.map q ≫ prodComparison DiagSet.toSSet X Y)]
    [WeakEquivalence (DiagSet.toSSet.map q' ≫ prodComparison DiagSet.toSSet X' Y')]
    (hr : WeakEquivalence ((DiagSet.toInfty 1).map r))
    (hq : r ≫ q = grayTensorToProd X Y)
    (hq' : r' ≫ q' = grayTensorToProd X' Y')
    (ht : r ≫ t = grayTensorBifunctor.map (f, g) ≫ r') :
    L.map (DiagSet.toSSet.map t) =
      (derivedGrayTensorComparisonIso L q).hom ≫
        L.map (prod.map (DiagSet.toSSet.map f) (DiagSet.toSSet.map g)) ≫
        (derivedGrayTensorComparisonIso L q').inv := by
  apply (cancel_mono (derivedGrayTensorComparisonIso L q').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact map_toSSet_derivedGrayTensorComparison_naturality L hX' hY' f g r r' q q' t hr hq hq' ht

theorem derivedGrayTensorComparisonIso_independent {H : Type*} [Category* H]
    (L : SSet.{u} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{u})]
    {X Y T T' : DiagSet.{u}} (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (hT' : IsInftyCategory 1 T')
    (r : grayTensor X Y ⟶ T) (r' : grayTensor X Y ⟶ T')
    (q : T ⟶ X ⨯ Y) (q' : T' ⟶ X ⨯ Y)
    [WeakEquivalence (DiagSet.toSSet.map q ≫ prodComparison DiagSet.toSSet X Y)]
    [WeakEquivalence (DiagSet.toSSet.map q' ≫ prodComparison DiagSet.toSSet X Y)]
    (hrm : Mono r) (hr : WeakEquivalence ((DiagSet.toInfty 1).map r))
    (hq : r ≫ q = grayTensorToProd X Y)
    (hq' : r' ≫ q' = grayTensorToProd X Y) :
    (∃ t : T ⟶ T', r ≫ t = r') ∧ ∀ t : T ⟶ T', r ≫ t = r' →
      L.map (DiagSet.toSSet.map t) =
        (derivedGrayTensorComparisonIso L q).hom ≫ (derivedGrayTensorComparisonIso L q').inv := by
  refine ⟨?_, fun t ht => ?_⟩
  · have : IsFibrant ((DiagSet.toInfty 1).obj T') := (isFibrant_infty_iff 1 _).2 hT'
    have : Cofibration ((DiagSet.toInfty 1).map r) := (cofibration_iff _).2 hrm
    let r'' : (DiagSet.toInfty 1).obj (grayTensor X Y) ⟶ (DiagSet.toInfty 1).obj T' := r'
    let sq : CommSq r'' ((DiagSet.toInfty 1).map r) (terminal.from _) (terminal.from _) :=
      ⟨terminal.hom_ext _ _⟩
    exact ⟨sq.lift, sq.fac_left⟩
  · have h := derivedGrayTensorComparisonIso_map_of_comp_eq L hX hY (𝟙 X) (𝟙 Y) r r' q q' t hr hq
      hq' (by rw [ht, show ((𝟙 X, 𝟙 Y) : (X, Y) ⟶ (X, Y)) = 𝟙 (X, Y) from rfl,
        CategoryTheory.Functor.map_id, Category.id_comp])
    rw [h, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, prod.map_id_id, L.map_id,
      Category.id_comp]

@[reassoc]
theorem map_fibrant_extension_comp_prodComparison {T X Y : DiagSet.{u}}
    (r : grayTensor X Y ⟶ T) (q : T ⟶ X ⨯ Y)
    (hq : r ≫ q = grayTensorToProd X Y) :
    DiagSet.toSSet.map r ≫
      (DiagSet.toSSet.map q ≫ prodComparison DiagSet.toSSet X Y) =
    prod.lift (DiagSet.toSSet.map (grayTensorFst X Y))
      (DiagSet.toSSet.map (grayTensorSnd X Y)) := by
  apply prod.hom_ext
  · rw [Category.assoc, Category.assoc, prodComparison_fst, ← Functor.map_comp,
      ← Functor.map_comp, ← Category.assoc, hq, grayTensorToProd, prod.lift_fst, prod.lift_fst]
  · rw [Category.assoc, Category.assoc, prodComparison_snd, ← Functor.map_comp,
      ← Functor.map_comp, ← Category.assoc, hq, grayTensorToProd, prod.lift_snd, prod.lift_snd]

noncomputable def DiagSet.Infty.grayTensorLeftAdjunction (n : ℕ∞) (X : DiagSet.{u}) :
    @Adjunction (DiagSet.Infty.{u} n) (DiagSet.Infty.category n) (DiagSet.Infty.{u} n)
      (DiagSet.Infty.category n) (grayTensorLeft X)
      (grayHomLeft X) :=
  Atoms.Diagrammatic.grayTensorLeftAdjunction X

noncomputable def DiagSet.Infty.grayTensorRightAdjunction (n : ℕ∞) (Y : DiagSet.{u}) :
    @Adjunction (DiagSet.Infty.{u} n) (DiagSet.Infty.category n) (DiagSet.Infty.{u} n)
      (DiagSet.Infty.category n) (grayTensorRight Y)
      (grayHomRight Y) :=
  Atoms.Diagrammatic.grayTensorRightAdjunction Y

theorem DiagSet.Infty.isQuillen_grayTensorLeftAdjunction_one (X : DiagSet.{u}) :
    (DiagSet.Infty.grayTensorLeftAdjunction 1 X).IsQuillen where
  cofibrations_le A B f hf :=
    have : @Mono DiagSet.{u} _ A B f := hf
    mono_grayTensorBifunctor_map (𝟙 X) f
  trivialCofibrations_le A B f hf :=
    have : @Mono DiagSet.{u} _ A B f := hf.1
    ⟨mono_grayTensorBifunctor_map (𝟙 X) f, (weakEquivalence_iff _).1
      (DiagSet.Infty.weakEquivalence_toInfty_one_grayTensorLeft_map X f
        ((weakEquivalence_iff _).2 hf.2))⟩

theorem DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one (Y : DiagSet.{u}) :
    (DiagSet.Infty.grayTensorRightAdjunction 1 Y).IsQuillen where
  cofibrations_le A B f hf :=
    have : @Mono DiagSet.{u} _ A B f := hf
    mono_grayTensorBifunctor_map f (𝟙 Y)
  trivialCofibrations_le A B f hf :=
    have : @Mono DiagSet.{u} _ A B f := hf.1
    ⟨mono_grayTensorBifunctor_map f (𝟙 Y), (weakEquivalence_iff _).1
      (DiagSet.Infty.weakEquivalence_toInfty_one_grayTensorRight_map Y f
        ((weakEquivalence_iff _).2 hf.2))⟩

end Atoms.Diagrammatic
