import Atoms.Diagrammatic.ClosedSubpresheafPushout
import Atoms.Diagrammatic.Joyal.Contraction
import Atoms.Diagrammatic.Joyal.JoinBox
import Atoms.Diagrammatic.Marked.Fibrancy

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Opposite
open Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape AugmentedSimplexCategory

universe u

namespace Atoms.Diagrammatic

def coneBoxSubset (A : Atom) (n : ℕ) : LowerSet (cone A (n + 1)).ogp where
  carrier := {y | (coneCoord A (n + 1) y).2 ≠ Finset.univ ∨
    ∀ c : A.ogp, (coneCoord A (n + 1) y).1 = c → c ∈ A.ogp.boundary ⊤ 0 true}
  lower' x y hyx hx := by
    obtain ⟨h₁, h₂⟩ := le_iff_coneCoord.1 hyx
    rcases hx with hx | hx
    · refine Or.inl fun hy => hx ?_
      rw [hy] at h₂
      exact Finset.univ_subset_iff.1 h₂
    · refine Or.inr fun c hc => ?_
      rw [hc] at h₁
      obtain ⟨c', hc', hcc'⟩ := WithBot.coe_le_iff.1 h₁
      exact (A.ogp.boundary ⊤ 0 true).lower hcc' (hx c' hc')

theorem mem_coneBoxSubset {A : Atom} {n : ℕ} {y : (cone A (n + 1)).ogp} :
    y ∈ coneBoxSubset A n ↔ (coneCoord A (n + 1) y).2 ≠ Finset.univ ∨
      ∀ c : A.ogp, (coneCoord A (n + 1) y).1 = c → c ∈ A.ogp.boundary ⊤ 0 true :=
  Iff.rfl

private theorem botVertices_ne_univ_iff (n : ℕ) (b : WithBot (simplex.{0} n)) :
    botVertices n b ≠ Finset.univ ↔ ∀ c : simplex.{0} n, b = c → grade ℕ c < n := by
  rw [Ne, ← Finset.card_eq_iff_eq_univ, card_botVertices, Fintype.card_fin]
  have hle : grade ℕ b ≤ n + 1 := by
    rw [← card_botVertices]
    exact (Finset.card_le_univ _).trans (Fintype.card_fin _).le
  induction b using WithBot.recBotCoe with
  | bot => simp
  | coe c =>
    rw [WithBot.grade_coe] at hle ⊢
    constructor
    · rintro h c' hc'
      rw [WithBot.coe_injective hc'] at h hle
      omega
    · intro h hc
      have := h c rfl
      omega

theorem mem_coneBoxSubset_iff (A : Atom) (n : ℕ) (p : join A.ogp (simplex n)) :
    (coneJoinSimplexIso A n).hom p ∈ coneBoxSubset A n ↔
      p ∈ MoleculeShape.joinBoxSubset A.toMoleculeShape n (A.ogp.boundary ⊤ 0 true) ⊤ := by
  refine Iff.trans ?_ (MoleculeShape.mem_joinBoxSubset A.toMoleculeShape n (p := p)).symm
  rw [mem_coneBoxSubset, coneCoord_coneJoinSimplexIso, botVertices_ne_univ_iff]
  exact (and_iff_right fun _ _ => LowerSet.mem_top).symm

private noncomputable def joinBoxArrowIso (A : Atom) (n : ℕ) :
    Arrow.mk (joinBox.{u} A.toMoleculeShape n (A.ogp.boundary ⊤ 0 true) ⊤) ≅
      Arrow.mk (closedSubpresheaf (cone A (n + 1)) (coneBoxSubset A n)).ι :=
  have : IsIso (closedSubpresheaf (cone A (n + 1)) ⊤).ι :=
    (Subfunctor.eq_top_iff_isIso _).1 (closedSubpresheaf_univ _)
  Arrow.isoMk
    (realizeRestrictIsoOfIso (MoleculeShape.joinSimplexRDC A.toMoleculeShape n) (cone A (n + 1))
      (coneJoinSimplexIso A n) _ _ (mem_coneBoxSubset_iff A n))
    (realizeRestrictIsoOfIso (MoleculeShape.joinSimplexRDC A.toMoleculeShape n) (cone A (n + 1))
      (coneJoinSimplexIso A n) _ ⊤
        (fun p => iff_of_true LowerSet.mem_top
          ((MoleculeShape.mem_joinSubset A.toMoleculeShape n).2 fun _ _ => LowerSet.mem_top)) ≪≫
      asIso (closedSubpresheaf (cone A (n + 1)) ⊤).ι) (by
    ext T g
    rfl)

theorem weakEquivalence_markedAboveFunctor_map_closedSubpresheaf_coneBoxSubset_ι (A : Atom)
    (n : ℕ) :
    WeakEquivalence ((MarkedDiagSet.Coinductive.markedAboveFunctor.{u} 1).map
      (closedSubpresheaf (cone A (n + 1)) (coneBoxSubset A n)).ι) := by
  refine (weakEquivalence_coinductive_iff 1
    ((MarkedDiagSet.markedAboveFunctor 1).map (closedSubpresheaf (cone A (n + 1))
      (coneBoxSubset A n)).ι)).2 ?_
  have := MorphismProperty.respectsIso_of_isStableUnderComposition
    (markedExactCylinder.isomorphisms_le_weakEquivalences (coinductiveGenerators 1))
  refine ((markedExactCylinder.{u}.weakEquivalences _).arrow_mk_iso_iff
    ((MarkedDiagSet.markedAboveFunctor 1).mapArrow.mapIso (joinBoxArrowIso A n))).1 ?_
  exact (weakEquivalence_coinductive_iff 1 _).1
    (weakEquivalence_markedAboveFunctor_map_joinBox_boundary 1 A.toMoleculeShape n 0 true
      (Or.inl rfl))

theorem exists_comp_eq_of_weakEquivalence_markedAboveFunctor_map {A B X : DiagSet.{u}}
    (i : A ⟶ B) [Mono i]
    (hi : WeakEquivalence ((MarkedDiagSet.Coinductive.markedAboveFunctor 1).map i))
    (hX : IsInftyCategory 1 X) (f : A ⟶ X) : ∃ g : B ⟶ X, i ≫ g = f := by
  have hfib := isFibrant_coinductive_natural 1 hX
  let f' : (MarkedDiagSet.markedAboveFunctor 1).obj A ⟶ MarkedDiagSet.natural.obj X :=
    Homotopical.MarkedPresheaf.homMk (X := MarkedDiagSet.markedAbove A 1) f fun V x hx => by
      refine (MarkedDiagSet.mem_marked_natural_iff X V _).2 ?_
      rcases (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hx with h | h
      · exact degenerate_isEquivalence X _ (isDegenerate_app f h)
      · exact hX.2 V _ (by exact_mod_cast h)
  let j := (MarkedDiagSet.toCoinductive 1).map ((MarkedDiagSet.markedAboveFunctor 1).map i)
  have : WeakEquivalence j := hi
  have : Cofibration j := by
    rw [cofibration_iff]
    exact MarkedDiagSet.mono_markedAboveFunctor_map 1 i
  have sq : CommSq ((MarkedDiagSet.toCoinductive 1).map f') j
      (terminal.from ((MarkedDiagSet.toCoinductive 1).obj (MarkedDiagSet.natural.obj X)))
      (terminal.from _) := ⟨terminal.hom_ext _ _⟩
  exact ⟨Homotopical.MarkedPresheaf.forget.map sq.lift,
    (Homotopical.MarkedPresheaf.forget.map_comp _ _).symm.trans
      (congrArg Homotopical.MarkedPresheaf.forget.map sq.fac_left)⟩

section Cover

variable {X : DiagSet.{u}} {V : Atom} (G : Subfunctor (ball.{u} V)) {J : Type u} (W : J → Atom)
  (u : ∀ j, W j ⟶ V) (x : ∀ j, X.obj (op (W j)))
  (hcov : ∀ {T : Atom} (f : T ⟶ V), ULift.up f ∈ G.obj (op T) → ∃ j, ∃ g : T ⟶ W j, g ≫ u j = f)
  (hx : ∀ {T : Atom} (j k : J) (g : T ⟶ W j) (g' : T ⟶ W k), g ≫ u j = g' ≫ u k →
    X.map g.op (x j) = X.map g'.op (x k))

private noncomputable def descOfCoverFun {T : Atom} (f : T ⟶ V) (hf : ULift.up f ∈ G.obj (op T)) :
    X.obj (op T) :=
  X.map (hcov f hf).choose_spec.choose.op (x (hcov f hf).choose)

include hx in
private theorem descOfCoverFun_eq {T : Atom} (f : T ⟶ V) (hf : ULift.up f ∈ G.obj (op T))
    (j : J) (g : T ⟶ W j) (hg : g ≫ u j = f) :
    descOfCoverFun G W u x hcov f hf = X.map g.op (x j) :=
  hx _ _ _ _ ((hcov f hf).choose_spec.choose_spec.trans hg.symm)

private noncomputable def descOfCover : G.toFunctor ⟶ X where
  app T := TypeCat.ofHom fun f => descOfCoverFun G W u x hcov f.1.down f.2
  naturality T T' h := by
    ext f
    obtain ⟨j, g, hg⟩ := hcov f.1.down f.2
    have h₁ := descOfCoverFun_eq G W u x hcov hx (h.unop ≫ f.1.down) (G.toFunctor.map h f).2 j
      (h.unop ≫ g) (by rw [Category.assoc, hg])
    have h₂ := descOfCoverFun_eq G W u x hcov hx f.1.down f.2 j g hg
    exact h₁.trans ((Functor.map_comp_apply X g.op h (x j)).trans
      (congrArg (X.map h) h₂.symm))

include hx in
private theorem descOfCover_app {T : Atom} {f : T ⟶ V} (hf : ULift.up f ∈ G.obj (op T)) (j : J)
    (g : T ⟶ W j) (hg : g ≫ u j = f) :
    (descOfCover G W u x hcov hx).app (op T) ⟨⟨f⟩, hf⟩ = X.map g.op (x j) :=
  descOfCoverFun_eq G W u x hcov hx f hf j g hg

end Cover

private theorem exists_comp_coneHom_injective {T A : Atom} {c a : AugmentedSimplexCategory}
    (g : T ⟶ cone A (card c)) (ι : c ⟶ a) :
    ∃ (d' : AugmentedSimplexCategory) (ι' : d' ⟶ c) (g' : T ⟶ cone A (card d'))
      (d : AugmentedSimplexCategory) (π : d' ⟶ d) (ε : d ⟶ a),
      g' ≫ coneHom A (toOrderHom ι') = g ∧ ι' ≫ ι = π ≫ ε ∧ Function.Injective (toFun ε) ∧
        Finset.univ.image (toFun ε) =
          (coneCoord A (card a) ((g ≫ coneHom A (toOrderHom ι)) T.top)).2 := by
  obtain ⟨d', ι', hι', himι'⟩ := exists_injective_image_eq c (coneCoord A (card c) (g T.top)).2
  obtain ⟨g', hg'⟩ := exists_comp_coneHom_eq g (σ := toOrderHom ι') hι' himι'.ge
  obtain ⟨d, π, ε, hπε, hε, himε⟩ := exists_comp_eq_injective (ι' ≫ ι)
  refine ⟨d', ι', g', d, π, ε, hg', hπε.symm, hε, ?_⟩
  rw [himε, coneCoord_comp_coneHom_apply_top, ← himι', Finset.image_image]
  exact Finset.image_congr fun i _ => toFun_comp_apply ι' ι i

variable {X : DiagSet.{u}} {A : Atom} {a : AugmentedSimplexCategory}

private theorem map_app_eq_map_app_of_comp_eq
    (t : (boundary a).toFunctor ⟶ (coneRestriction A).obj X) {T : Atom}
    {c d d' : AugmentedSimplexCategory} (e₁ : (boundary a).toFunctor.obj (op c))
    (e₂ : (boundary a).toFunctor.obj (op d)) (ι' : d' ⟶ c) (π : d' ⟶ d)
    (g' : T ⟶ cone A (card d')) (hc : ι' ≫ e₁.1.down = π ≫ e₂.1.down) :
    X.map (g' ≫ coneHom A (toOrderHom ι')).op (t.app (op c) e₁) =
      X.map (g' ≫ coneHom A (toOrderHom π)).op (t.app (op d) e₂) := by
  refine (Functor.map_comp_apply X (coneHom A (toOrderHom ι')).op g'.op _).trans
    (Eq.trans ?_ (Functor.map_comp_apply X (coneHom A (toOrderHom π)).op g'.op _).symm)
  refine congrArg (X.map g'.op) ?_
  have n₁ := NatTrans.naturality_apply t ι'.op e₁
  have n₂ := NatTrans.naturality_apply t π.op e₂
  refine n₁.symm.trans (Eq.trans ?_ n₂)
  exact congrArg (t.app (op d')) (Subtype.ext (ULift.ext _ _ hc))

private theorem map_app_eq_of_injective
    (t : (boundary a).toFunctor ⟶ (coneRestriction A).obj X) {T : Atom}
    {d₁ d₂ : AugmentedSimplexCategory} (e₁ : (boundary a).toFunctor.obj (op d₁))
    (e₂ : (boundary a).toFunctor.obj (op d₂))
    (hi₁ : Function.Injective (toFun e₁.1.down)) (hi₂ : Function.Injective (toFun e₂.1.down))
    (him : Finset.univ.image (toFun e₁.1.down) = Finset.univ.image (toFun e₂.1.down))
    (h₁ : T ⟶ cone A (card d₁)) (h₂ : T ⟶ cone A (card d₂))
    (heq : h₁ ≫ coneHom A (toOrderHom e₁.1.down) = h₂ ≫ coneHom A (toOrderHom e₂.1.down)) :
    X.map h₁.op (t.app (op d₁) e₁) = X.map h₂.op (t.app (op d₂) e₂) := by
  obtain ⟨hd, he⟩ := eq_of_injective_of_image_eq e₁.1.down e₂.1.down hi₁ hi₂ him
  obtain rfl : d₁ = d₂ := hd
  rw [eqToHom_refl, Category.id_comp] at he
  obtain rfl : e₁ = e₂ := Subtype.ext (ULift.ext _ _ he)
  have := mono_of_isInclusionHom _ (isInclusionHom_coneHom A (σ := toOrderHom e₁.1.down) hi₁)
  rw [(cancel_mono _).1 heq]

private theorem map_app_eq_map_yonedaEquiv
    (t : (boundary a).toFunctor ⟶ (coneRestriction A).obj X)
    (b : uliftYoneda.{u}.obj a ⟶ (coneRestriction atomPoint).obj X)
    (sq : CommSq t (boundary a).ι ((coneRestrictionMap (outputVertex A)).app X) b) {T : Atom}
    {d : AugmentedSimplexCategory} (e : (boundary a).toFunctor.obj (op d))
    (hi : Function.Injective (toFun e.1.down)) (h : T ⟶ cone A (card d))
    (g' : T ⟶ cone atomPoint (card a))
    (heq : h ≫ coneHom A (toOrderHom e.1.down) = g' ≫ coneMap (outputVertex A) (card a)) :
    X.map h.op (t.app (op d) e) =
      X.map g'.op (uliftYonedaEquiv (C := AugmentedSimplexCategory) b) := by
  have hS : (coneCoord atomPoint (card a) (g' T.top)).2 ⊆
      Finset.univ.image (toOrderHom e.1.down) := by
    have h₁ := congrArg (fun f => (coneCoord A (card a) (f T.top)).2) heq
    simp only [coneCoord_comp_coneHom_apply_top, coneCoord_comp_coneMap_apply_top] at h₁
    rw [← h₁]
    exact Finset.image_subset_image (Finset.subset_univ _)
  obtain ⟨g'', rfl⟩ := exists_comp_coneHom_eq g' hi hS
  have hh : h = g'' ≫ coneMap (outputVertex A) (card d) := by
    have := mono_of_isInclusionHom _ (isInclusionHom_coneHom A (σ := toOrderHom e.1.down) hi)
    refine (cancel_mono (coneHom A (toOrderHom e.1.down))).1 ?_
    rw [heq, Category.assoc, Category.assoc, coneHom_comp_coneMap]
  subst hh
  refine (Functor.map_comp_apply X (coneMap (outputVertex A) (card d)).op g''.op _).trans
    (Eq.trans ?_
      (Functor.map_comp_apply X (coneHom atomPoint (toOrderHom e.1.down)).op g''.op _).symm)
  have hb : ((coneRestriction atomPoint).obj X).map e.1.down.op (uliftYonedaEquiv b) =
      b.app (op d) e.1 := by
    rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_comp, Quiver.Hom.unop_op,
      uliftYonedaEquiv_uliftYoneda_map]
  refine congrArg (X.map g''.op) (Eq.trans ?_ hb.symm)
  exact ConcreteCategory.congr_hom (NatTrans.congr_app sq.w (op d)) e

private theorem not_mem_boundary_star {c : AugmentedSimplexCategory}
    (f : c ⟶ WithInitial.star) : ULift.up f ∉ (boundary.{u} WithInitial.star).obj (op c) :=
  fun hf => hf fun i => i.elim0

private theorem hasLiftingProperty_boundary_star_coneRestrictionMap_outputVertex (X : DiagSet.{u})
    (A : Atom) :
    HasLiftingProperty (boundary WithInitial.star).ι
      ((coneRestrictionMap (outputVertex A)).app X) := by
  refine ⟨fun {t b} sq => ⟨⟨⟨uliftYonedaEquiv.symm
    (((coneRestrictionMap (toAtomPoint A)).app X).app _ (uliftYonedaEquiv b)), ?_, ?_⟩⟩⟩⟩
  · ext c ⟨⟨f⟩, hf⟩
    exact absurd hf (not_mem_boundary_star.{u} f)
  · refine uliftYonedaEquiv.injective ?_
    rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    have h (q : X.obj (op (cone atomPoint 0))) :
        X.map (coneMap (outputVertex A) 0).op (X.map (coneMap (toAtomPoint A) 0).op q) = q := by
      rw [← Functor.map_comp_apply, ← op_comp, ← coneMap_comp,
        Subsingleton.elim (outputVertex A ≫ toAtomPoint A) (𝟙 atomPoint), coneMap_id, op_id,
        Functor.map_id_apply]
    exact h _

private theorem mem_boundary_of_image_eq {T : Atom} {c d : AugmentedSimplexCategory}
    (e : (boundary.{u} a).toFunctor.obj (op c)) (g : T ⟶ cone A (card c)) (ε : d ⟶ a)
    (him : Finset.univ.image (toFun ε) =
      (coneCoord A (card a) ((g ≫ coneHom A (toOrderHom e.1.down)) T.top)).2) :
    ULift.up ε ∈ (boundary.{u} a).obj (op d) := by
  intro hsurj
  refine e.2 fun k => ?_
  have hk : k ∈ Finset.univ.image (toFun ε) := by
    obtain ⟨j, hj⟩ := hsurj k
    exact hj ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j)
  rw [him, coneCoord_comp_coneHom_apply_top] at hk
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hk
  exact ⟨i, hi⟩

private theorem hasLiftingProperty_boundary_of_coneRestrictionMap_outputVertex (X : DiagSet.{u})
    (hX : IsInftyCategory 1 X) (A : Atom) (m : SimplexCategory) :
    HasLiftingProperty (boundary (WithInitial.of m)).ι
      ((coneRestrictionMap (outputVertex A)).app X) := by
  refine ⟨fun {t b} sq => ?_⟩
  let J := Option (Σ c : AugmentedSimplexCategory,
    (boundary (WithInitial.of m)).toFunctor.obj (op c))
  let W : J → Atom := fun j => Option.elim j (cone atomPoint (m.len + 1))
    fun e => cone A (card e.1)
  let u : (j : J) → W j ⟶ cone A (m.len + 1) := fun j => match j with
    | none => coneMap (outputVertex A) (m.len + 1)
    | some e => coneHom A (toOrderHom e.2.1.down)
  let x : (j : J) → X.obj (op (W j)) := fun j => match j with
    | none => uliftYonedaEquiv (C := AugmentedSimplexCategory) b
    | some e => t.app (op e.1) e.2
  let G := closedSubpresheaf (cone A (m.len + 1)) (coneBoxSubset A m.len)
  have hcov : ∀ {T : Atom} (f : T ⟶ cone A (m.len + 1)), ULift.up f ∈ G.obj (op T) →
      ∃ j, ∃ g : T ⟶ W j, g ≫ u j = f := by
    intro T f hf
    rcases mem_coneBoxSubset.1 (hf T.top) with hσ | hbase
    · obtain ⟨d, ε, hε, him⟩ :=
        exists_injective_image_eq (WithInitial.of m) (coneCoord A (m.len + 1) (f T.top)).2
      have hb : ULift.up ε ∈ (boundary.{u} (WithInitial.of m)).obj (op d) := fun hsurj => by
        refine hσ ?_
        rw [← him]
        exact Finset.eq_univ_of_forall fun k => by
          obtain ⟨j, hj⟩ := hsurj k
          exact hj ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j)
      obtain ⟨g, hg⟩ := exists_comp_coneHom_eq f (σ := toOrderHom ε) hε him.ge
      exact ⟨some ⟨d, ⟨⟨ε⟩, hb⟩⟩, g, hg⟩
    · obtain ⟨g, hg⟩ := exists_comp_coneMap_eq (outputVertex A) (isInclusionHom_outputVertex A)
        f fun c hc => by
          have h : c ∈ (A.ogp.boundary ⊤ 0 true : Set A.ogp) := hbase c hc
          rw [boundary_univ_zero_true_eq_singleton, Set.mem_singleton_iff] at h
          rw [h, outputVertex_apply]
      exact ⟨none, g, hg⟩
  have hx : ∀ {T : Atom} (j k : J) (g : T ⟶ W j) (g' : T ⟶ W k), g ≫ u j = g' ≫ u k →
      X.map g.op (x j) = X.map g'.op (x k) := by
    have hred : ∀ {T : Atom} (c : AugmentedSimplexCategory)
        (e : (boundary (WithInitial.of m)).toFunctor.obj (op c)) (g : T ⟶ cone A (card c)),
        ∃ (d : AugmentedSimplexCategory) (e' : (boundary (WithInitial.of m)).toFunctor.obj (op d))
          (h : T ⟶ cone A (card d)), Function.Injective (toFun e'.1.down) ∧
          Finset.univ.image (toFun e'.1.down) =
            (coneCoord A (card (WithInitial.of m))
              ((g ≫ coneHom A (toOrderHom e.1.down)) T.top)).2 ∧
          h ≫ coneHom A (toOrderHom e'.1.down) = g ≫ coneHom A (toOrderHom e.1.down) ∧
          X.map g.op (t.app (op c) e) = X.map h.op (t.app (op d) e') := by
      intro T c e g
      obtain ⟨d', ι', g', d, π, ε, hg, hc, hi, him⟩ := exists_comp_coneHom_injective g e.1.down
      have hb := mem_boundary_of_image_eq e g ε him
      refine ⟨d, ⟨⟨ε⟩, hb⟩, g' ≫ coneHom A (toOrderHom π), hi, him, ?_, ?_⟩
      · rw [Category.assoc, ← coneHom_toOrderHom_comp, ← hc, coneHom_toOrderHom_comp, ← hg,
          Category.assoc]
      · rw [← hg]
        exact map_app_eq_map_app_of_comp_eq t e ⟨⟨ε⟩, hb⟩ ι' π g' hc
    intro T j k g g' hgg'
    rcases j with _ | ⟨c, e⟩ <;> rcases k with _ | ⟨c', e'⟩
    · have := mono_of_isInclusionHom _
        (isInclusionHom_coneMap (isInclusionHom_outputVertex A) (m.len + 1))
      rw [(cancel_mono (coneMap (outputVertex A) (m.len + 1))).1 hgg']
    · obtain ⟨d, e₁, h, hi, -, hh, hv⟩ := hred c' e' g'
      exact (hv.trans (map_app_eq_map_yonedaEquiv t b sq e₁ hi h g (hh.trans hgg'.symm))).symm
    · obtain ⟨d, e₁, h, hi, -, hh, hv⟩ := hred c e g
      exact hv.trans (map_app_eq_map_yonedaEquiv t b sq e₁ hi h g' (hh.trans hgg'))
    · obtain ⟨d₁, e₁, h₁, hi₁, him₁, hh₁, hv₁⟩ := hred c e g
      obtain ⟨d₂, e₂, h₂, hi₂, him₂, hh₂, hv₂⟩ := hred c' e' g'
      refine hv₁.trans (Eq.trans ?_ hv₂.symm)
      refine map_app_eq_of_injective t e₁ e₂ hi₁ hi₂ ?_ h₁ h₂ ?_
      · rw [him₁, him₂]
        exact congrArg (fun f => (coneCoord A (m.len + 1) (f T.top)).2) hgg'
      · rw [hh₁, hh₂]
        exact hgg'
  have hmem : ∀ (c : AugmentedSimplexCategory)
      (e : (boundary (WithInitial.of m)).toFunctor.obj (op c)),
      ULift.up (coneHom A (toOrderHom e.1.down)) ∈ G.obj (op (cone A (card c))) := by
    intro c e t'
    refine mem_coneBoxSubset.2 (Or.inl fun hu => e.2 fun k => ?_)
    have h := coneCoord_coneHom A (toOrderHom e.1.down) (t' : WithBot _)
    rw [WithBot.map_coe] at h
    have hu' := (congrArg Prod.snd h).symm.trans hu
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (hu' ▸ Finset.mem_univ k)
    exact ⟨i, hi⟩
  have hmem' : ULift.up (coneMap (outputVertex A) (m.len + 1)) ∈
      G.obj (op (cone atomPoint (m.len + 1))) := by
    intro t'
    refine mem_coneBoxSubset.2 (Or.inr fun c hc => ?_)
    have h := coneCoord_coneMap (outputVertex A) (m.len + 1) (t' : WithBot _)
    rw [WithBot.map_coe] at h
    rw [h] at hc
    obtain ⟨v, -, hv⟩ := WithBot.map_eq_some_iff.1 hc
    rw [← hv, outputVertex_apply]
    change outputVertexElem A ∈ (A.ogp.boundary ⊤ 0 true : Set A.ogp)
    rw [boundary_univ_zero_true_eq_singleton]
    exact Set.mem_singleton _
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_weakEquivalence_markedAboveFunctor_map G.ι
    (weakEquivalence_markedAboveFunctor_map_closedSubpresheaf_coneBoxSubset_ι A m.len) hX
    (descOfCover G W u x hcov hx)
  have hmapψ : ∀ {T : Atom} (f : T ⟶ cone A (m.len + 1)),
      X.map f.op (uliftYonedaEquiv ψ) = ψ.app (op T) ⟨f⟩ := fun f =>
    (uliftYonedaEquiv_naturality ψ f.op).trans
      (congrArg (ψ.app _) (congrArg ULift.up (Category.id_comp f)))
  refine ⟨⟨⟨uliftYonedaEquiv.symm
    (uliftYonedaEquiv (C := Atom) ψ : ((coneRestriction A).obj X).obj (op (WithInitial.of m))),
    ?_, ?_⟩⟩⟩
  · ext ⟨c⟩ e
    have h₁ := ConcreteCategory.congr_hom (NatTrans.congr_app hψ (op (cone A (card c))))
      ⟨⟨coneHom A (toOrderHom e.1.down)⟩, hmem c e⟩
    refine (hmapψ (coneHom A (toOrderHom e.1.down))).trans (h₁.trans ?_)
    refine (descOfCover_app G W u x hcov hx (hmem c e) (some ⟨c, e⟩) (𝟙 _)
      (Category.id_comp _)).trans ?_
    exact Functor.map_id_apply X _ _
  · have h₁ := ConcreteCategory.congr_hom
      (NatTrans.congr_app hψ (op (cone atomPoint (m.len + 1))))
      ⟨⟨coneMap (outputVertex A) (m.len + 1)⟩, hmem'⟩
    have h₂ : X.map (coneMap (outputVertex A) (m.len + 1)).op (uliftYonedaEquiv (C := Atom) ψ) =
        uliftYonedaEquiv (C := AugmentedSimplexCategory) b :=
      (hmapψ (coneMap (outputVertex A) (m.len + 1))).trans (h₁.trans
        ((descOfCover_app G W u x hcov hx hmem' none (𝟙 _) (Category.id_comp _)).trans
          (Functor.map_id_apply X _ _)))
    refine uliftYonedaEquiv.injective ((uliftYonedaEquiv_comp _ _).trans ?_)
    refine (congrArg (((coneRestrictionMap (outputVertex A)).app X).app (op (WithInitial.of m)))
      ((uliftYonedaEquiv (C := AugmentedSimplexCategory) (X := WithInitial.of m)
        (F := (coneRestriction A).obj X)).apply_symm_apply
          (uliftYonedaEquiv (C := Atom) ψ))).trans ?_
    exact h₂

theorem hasLiftingProperty_boundary_coneRestrictionMap_outputVertex (X : DiagSet.{u})
    (hX : IsInftyCategory 1 X) (A : Atom) (a : AugmentedSimplexCategory) :
    HasLiftingProperty (boundary a).ι ((coneRestrictionMap (outputVertex A)).app X) := by
  cases a with
  | star => exact hasLiftingProperty_boundary_star_coneRestrictionMap_outputVertex X A
  | of m => exact hasLiftingProperty_boundary_of_coneRestrictionMap_outputVertex X hX A m

end Atoms.Diagrammatic
