import Atoms.Homotopical.Simplicial.FinalObject
import Atoms.Homotopical.Simplicial.ZeroObject
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.InitialExtension
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

open CategoryTheory Limits Simplicial MonoidalCategory MonoidalClosed HomotopicalAlgebra
  MorphismProperty Opposite

universe u

namespace SSet

variable {X : SSet.{u}}

private noncomputable def boundaryArrowIsoOp (n : ℕ) :
    Arrow.mk (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex).ι ≅
      Arrow.mk (opFunctor.map ∂Δ[n].ι) :=
  arrowIsoOfPreimage (stdSimplex.opIso ⦋n⦌).symm ∂Δ[n].op ∂Δ[n] (op_boundary n)

private lemma boundaryArrowIsoOp_app_lastVertex {n : ℕ} (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X) :
    ((boundaryArrowIsoOp (n + 1)).hom.left ≫ opFunctor.map b).app _ (boundary.lastVertex n) =
      opObjEquiv.symm (b.app _ (boundary.firstVertex n)) := by
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, opFunctor_map]
  congr 2
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  fin_cases i
  exact Fin.rev_last _

theorem isInitialObject_iff_extend_boundary [X.Quasicategory] (x : X _⦋0⦌) :
    IsInitialObject x ↔ ∀ (n : ℕ) (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X),
      b.app _ (boundary.firstVertex n) = x →
        ∃ c : Δ[n + 1] ⟶ X, (∂Δ[n + 1]).ι ≫ c = b := by
  rw [IsInitialObject, isFinal_iff_extend_boundary]
  let F := opEquivalence.{u}.fullyFaithfulFunctor
  refine forall_congr' fun n ↦ ⟨fun h b hb ↦ ?_, fun h b' hb' ↦ ?_⟩
  · let φ := boundaryArrowIsoOp.{u} (n + 1)
    obtain ⟨c', hc'⟩ := h (φ.hom.left ≫ opFunctor.map b)
      (by rw [boundaryArrowIsoOp_app_lastVertex, hb])
    refine ⟨F.preimage (φ.inv.right ≫ c'), F.map_injective ?_⟩
    rw [Functor.map_comp, F.map_preimage]
    have hw : opFunctor.map ∂Δ[n + 1].ι ≫ φ.inv.right = φ.inv.left ≫ ∂Δ[n + 1].ι :=
      (Arrow.w φ.inv).symm
    change opFunctor.map ∂Δ[n + 1].ι ≫ φ.inv.right ≫ c' = opFunctor.map b
    rw [reassoc_of% hw, hc', Arrow.inv_hom_id_left_assoc]
  · let φ := boundaryArrowIsoOp.{u} (n + 1)
    have hb : φ.hom.left ≫ opFunctor.map (F.preimage (φ.inv.left ≫ b')) = b' := by
      change φ.hom.left ≫ opEquivalence.functor.map (F.preimage (φ.inv.left ≫ b')) = b'
      rw [F.map_preimage]
      exact Arrow.hom_inv_id_left_assoc φ b'
    obtain ⟨c, hc⟩ := h (F.preimage (φ.inv.left ≫ b')) (opObjEquiv.symm.injective
      ((boundaryArrowIsoOp_app_lastVertex _).symm.trans
        ((by rw [hb] : ((φ.hom.left ≫ opFunctor.map (F.preimage (φ.inv.left ≫ b'))).app _
          (boundary.lastVertex n)) = b'.app _ (boundary.lastVertex n)).trans hb')))
    refine ⟨φ.hom.right ≫ opFunctor.map c, ?_⟩
    have hw : ∂Δ[n + 1].ι ≫ φ.hom.right = φ.hom.left ≫ opFunctor.map ∂Δ[n + 1].ι :=
      Arrow.w φ.hom
    rw [reassoc_of% hw, ← Functor.map_comp, hc, hb]

private lemma const_app_zero {L Z : SSet.{u}} (v : L _⦋0⦌) (s : Z _⦋0⦌) :
    (stdSimplex.isTerminalObj₀.from Z ≫ yonedaEquiv.symm v).app (op ⦋0⦌) s = v := by
  change L.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op v = v
  rw [SimplexCategory.hom_zero_zero (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0), op_id,
    Functor.map_id_apply]

private lemma lift_const_app {L Z : SSet.{u}} (v : L _⦋0⦌) (s : Z _⦋0⦌) :
    (CartesianMonoidalCategory.lift (stdSimplex.isTerminalObj₀.from Z ≫ yonedaEquiv.symm v)
      (𝟙 Z)).app (op ⦋0⦌) s = ((v, s) : (L ⊗ Z) _⦋0⦌) :=
  Prod.ext (const_app_zero v s) rfl

private structure Side (X : SSet.{u}) where
  vtx : ∀ m : ℕ, Fin (m + 1)
  vtx_epi : ∀ {m m' : ℕ} (f : ⦋m⦌ ⟶ ⦋m'⦌) [Epi f], f.toOrderHom (vtx m) = vtx m'
  Good : X _⦋0⦌ → Prop
  bvtx : ∀ n : ℕ, (∂Δ[n + 1] : SSet.{u}) _⦋0⦌
  bvtx_val : ∀ n : ℕ, (bvtx n).1 = stdSimplex.obj₀Equiv.symm (vtx (n + 1))
  extend : ∀ (n : ℕ) (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X), Good (b.app _ (bvtx n)) →
    ∃ c : (Δ[n + 1] : SSet.{u}) ⟶ X, (∂Δ[n + 1]).ι ≫ c = b
  sub : X.Subcomplex
  mem_sub : ∀ ω : X _⦋0⦌, ω ∈ sub.obj (op ⦋0⦌) ↔ Good ω
  sub_full : ∀ {n : ℕ} (σ : X _⦋n⦌),
    (∀ i : Fin (n + 1), X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op σ ∈ sub.obj (op ⦋0⦌)) →
      σ ∈ sub.obj (op ⦋n⦌)

private noncomputable abbrev Side.at {X : SSet.{u}} (Z : Side X) {L : SSet.{u}} (v : L _⦋0⦌) :
    ((ihom L).obj X).Subcomplex :=
  Z.sub.preimage (evalVertex v X)

private lemma epi_apply_last {m m' : ℕ} (f : ⦋m⦌ ⟶ ⦋m'⦌) [hf : Epi f] :
    f.toOrderHom (Fin.last m) = Fin.last m' := by
  obtain ⟨a, ha⟩ := (SimplexCategory.epi_iff_surjective.1 hf) (Fin.last m')
  exact le_antisymm (Fin.le_last _) (ha ▸ f.toOrderHom.monotone (Fin.le_last a))

private lemma epi_apply_zero {m m' : ℕ} (f : ⦋m⦌ ⟶ ⦋m'⦌) [hf : Epi f] :
    f.toOrderHom 0 = 0 := by
  obtain ⟨a, ha⟩ := (SimplexCategory.epi_iff_surjective.1 hf) 0
  exact le_antisymm (ha ▸ f.toOrderHom.monotone (Fin.zero_le a)) (Fin.zero_le _)

private lemma vertex_eq {X : SSet.{u}} (Z : Side X) {L : SSet.{u}} (T : L.Subcomplex) (v : L _⦋0⦌)
    (hL : ∀ (m : ℕ) (σ : L _⦋m⦌), σ ∈ L.nonDegenerate m → σ ∉ T.obj (op ⦋m⦌) →
      L.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ (Z.vtx m)).op σ = v) {m : ℕ} (τ : L _⦋m⦌)
    (hτ : τ ∉ T.obj (op ⦋m⦌)) :
    L.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ (Z.vtx m)).op τ = v := by
  obtain ⟨m', f, hf, y, rfl⟩ := exists_nonDegenerate (X := L) τ
  have hy : (y : L _⦋m'⦌) ∉ T.obj (op ⦋m'⦌) := fun h ↦ hτ (T.map f.op h)
  rw [← hL m' y y.2 hy, ← Functor.map_comp_apply, ← op_comp, SimplexCategory.const_comp,
    Z.vtx_epi]

private lemma lift_succ_at (Z : Side X) {L : SSet.{u}} (T : L.Subcomplex)
    (v : L _⦋0⦌)
    (hL : ∀ (m : ℕ) (σ : L _⦋m⦌), σ ∈ L.nonDegenerate m → σ ∉ T.obj (op ⦋m⦌) →
      L.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ (Z.vtx m)).op σ = v) (n : ℕ)
    (a : (∂Δ[n + 1] : SSet.{u}) ⟶ (Z.at v : SSet.{u}))
    (b : (Δ[n + 1] : SSet.{u}) ⟶ (ihom (T : SSet.{u})).obj X)
    (w : a ≫ (Z.at v).ι ≫ (pre T.ι).app X = (∂Δ[n + 1]).ι ≫ b) :
    ∃ l : (Δ[n + 1] : SSet.{u}) ⟶ (Z.at v : SSet.{u}),
      (∂Δ[n + 1]).ι ≫ l = a ∧
      l ≫ (Z.at v).ι ≫ (pre T.ι).app X = b := by
  have hw : (T.ι ▷ (∂Δ[n + 1] : SSet.{u})) ≫ uncurry (a ≫ (Z.at v).ι) =
      ((T : SSet.{u}) ◁ (∂Δ[n + 1]).ι) ≫ uncurry b := by
    rw [← uncurry_pre_app, ← uncurry_natural_left, ← w, Category.assoc]
  let U := Subcomplex.unionProd T (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex)
  let g : (U : SSet.{u}) ⟶ X := (Subcomplex.unionProd.isPushout T ∂Δ[n + 1]).desc
    (uncurry (a ≫ (Z.at v).ι)) (uncurry b) hw
  have hmem (s : (Δ[n + 1] : SSet.{u}) _⦋0⦌) :
      s ∈ (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex).obj (op ⦋0⦌) := by
    rw [boundary_obj_eq_univ 0 (n + 1)]
    trivial
  have h0 (s : (∂Δ[n + 1] : SSet.{u}) _⦋0⦌) :
      Z.Good (g.app _ ⟨(v, s.1), (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl s.2)⟩) := by
    have h1 : g.app _ ⟨(v, s.1), (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl s.2)⟩ =
        (uncurry (a ≫ (Z.at v).ι)).app _
          ((v, s) : (L ⊗ (∂Δ[n + 1] : SSet.{u})) _⦋0⦌) :=
      (ConcreteCategory.congr_hom (congr_app
        ((Subcomplex.unionProd.isPushout T ∂Δ[n + 1]).inl_desc _ _ hw) _)
        ((v, s) : (L ⊗ (∂Δ[n + 1] : SSet.{u})) _⦋0⦌))
    have h2 := ConcreteCategory.congr_hom (congr_app
      (comp_evalVertex v (a ≫ (Z.at v).ι)) _) s
    have h3 : (uncurry (a ≫ (Z.at v).ι)).app _
        ((v, s) : (L ⊗ (∂Δ[n + 1] : SSet.{u})) _⦋0⦌) =
          (evalVertex v X).app _ ((a.app _ s).1) := by
      rw [← lift_const_app v s]
      exact h2.symm
    rw [h1, h3]
    exact (Z.mem_sub _).1 (a.app _ s).2
  have hB : ∀ (m : ℕ) (σ : (L ⊗ (Δ[n + 1] : SSet.{u})) _⦋m⦌),
      σ ∈ (L ⊗ (Δ[n + 1] : SSet.{u})).nonDegenerate m → σ ∉ Set.range (U.ι.app _) →
      ∃ x : (U : SSet.{u}) _⦋0⦌, U.ι.app _ x =
        (L ⊗ (Δ[n + 1] : SSet.{u})).map
          (SimplexCategory.const ⦋0⦌ ⦋m⦌ (Z.vtx m)).op σ ∧
          Z.Good (g.app _ x) := by
    intro m σ _ hσ
    have hT : σ.1 ∉ T.obj (op ⦋m⦌) := fun h ↦
      hσ ⟨⟨σ, (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inr h)⟩, rfl⟩
    let s := Δ[n + 1].map (SimplexCategory.const ⦋0⦌ ⦋m⦌ (Z.vtx m)).op σ.2
    have hs : s ∈ (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex).obj (op ⦋0⦌) := hmem s
    refine ⟨⟨(v, s), (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl hs)⟩,
      Prod.ext (vertex_eq Z T v hL σ.1 hT).symm rfl, h0 ⟨s, hs⟩⟩
  obtain ⟨c, hc⟩ := exists_extension_of_mono_of_vertex U.ι g Z.Good Z.vtx Z.bvtx Z.bvtx_val
    Z.extend hB
  have hvert (j : (Δ[n + 1] : SSet.{u}) _⦋0⦌) :
      Z.Good (c.app _ ((v, j) : (L ⊗ (Δ[n + 1] : SSet.{u})) _⦋0⦌)) := by
    have := h0 ⟨j, hmem j⟩
    have e : c.app _ ((v, j) : (L ⊗ (Δ[n + 1] : SSet.{u})) _⦋0⦌) = g.app _
        ⟨(v, j), (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl (hmem j))⟩ :=
      ConcreteCategory.congr_hom (congr_app hc (op ⦋0⦌))
        ⟨(v, j), (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl (hmem j))⟩
    rw [e]
    exact this
  have hle : Subcomplex.range (curry c) ≤ Z.at v := by
    rintro ⟨k⟩ _ ⟨τ, rfl⟩
    refine Z.sub_full _ fun i ↦ (Z.mem_sub _).2 ?_
    have h1 := NatTrans.naturality_apply (curry c ≫ evalVertex v X)
      (SimplexCategory.const ⦋0⦌ k i).op τ
    have h2 : (curry c ≫ evalVertex v X).app (op ⦋0⦌)
        (Δ[n + 1].map (SimplexCategory.const ⦋0⦌ k i).op τ) =
          c.app _ ((v, Δ[n + 1].map (SimplexCategory.const ⦋0⦌ k i).op τ) :
            (L ⊗ (Δ[n + 1] : SSet.{u})) _⦋0⦌) := by
      rw [comp_evalVertex, uncurry_curry]
      exact congrArg (c.app _) (lift_const_app v _)
    have h3 : Z.Good ((curry c ≫ evalVertex v X).app (op ⦋0⦌)
        (Δ[n + 1].map (SimplexCategory.const ⦋0⦌ k i).op τ)) := by
      rw [h2]
      exact hvert _
    exact cast (congrArg Z.Good h1) h3
  refine ⟨Subcomplex.lift (curry c) hle, ?_, ?_⟩
  · rw [← cancel_mono (Z.at v).ι, Category.assoc, Subcomplex.lift_ι]
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, ← Subcomplex.unionProd.ι₁_ι, Category.assoc, hc]
    exact (Subcomplex.unionProd.isPushout T ∂Δ[n + 1]).inl_desc _ _ hw
  · rw [Subcomplex.lift_ι_assoc]
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, ← Subcomplex.unionProd.ι₂_ι, Category.assoc, hc]
    exact (Subcomplex.unionProd.isPushout T ∂Δ[n + 1]).inr_desc _ _ hw

private lemma lift_zero_at (Z : Side X) {L : SSet.{u}} (T : L.Subcomplex)
    (v : L _⦋0⦌) (hv : v ∉ T.obj (op ⦋0⦌))
    (hL : ∀ (m : ℕ) (σ : L _⦋m⦌), σ ∈ L.nonDegenerate m → σ ∉ T.obj (op ⦋m⦌) →
      L.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ (Z.vtx m)).op σ = v)
    (hX : ∃ x : X _⦋0⦌, Z.Good x) (b : (Δ[0] : SSet.{u}) ⟶ (ihom (T : SSet.{u})).obj X) :
    ∃ l : (Δ[0] : SSet.{u}) ⟶ (Z.at v : SSet.{u}),
      l ≫ (Z.at v).ι ≫ (pre T.ι).app X = b := by
  obtain ⟨x, hx⟩ := hX
  let V : L.Subcomplex := Subcomplex.ofSimplex v
  let S : L.Subcomplex := T ⊔ V
  have hTV : T ⊓ V = ⊥ := by
    refine Subfunctor.ext (funext fun k ↦ Set.ext fun y ↦ ?_)
    refine ⟨fun ⟨hyT, hyV⟩ ↦ ?_, fun h ↦ h.elim⟩
    obtain ⟨f, rfl⟩ := (Subcomplex.mem_ofSimplex_obj_iff v y).1 hyV
    refine (hv ?_).elim
    have : L.map (SimplexCategory.const ⦋0⦌ k.unop 0).op (L.map f.op v) ∈
        T.obj (op ⦋0⦌) :=
      T.map (SimplexCategory.const ⦋0⦌ k.unop 0).op hyT
    rwa [← Functor.map_comp_apply, ← op_comp, SimplexCategory.hom_zero_zero
      (SimplexCategory.const ⦋0⦌ k.unop 0 ≫ f), op_id, Functor.map_id_apply] at this
  have sq : Subcomplex.BicartSq (⊥ : L.Subcomplex) T V S := ⟨rfl, hTV⟩
  let bT : (T : SSet.{u}) ⟶ X := CartesianMonoidalCategory.lift (𝟙 _)
    (stdSimplex.isTerminalObj₀.from _) ≫ uncurry b
  let bV : (V : SSet.{u}) ⟶ X := stdSimplex.isTerminalObj₀.from _ ≫ yonedaEquiv.symm x
  let g : (S : SSet.{u}) ⟶ X := sq.isPushout.desc bT bV (Subcomplex.isInitialBot.hom_ext _ _)
  have hgV : g.app _ ⟨v, Or.inr (Subcomplex.mem_ofSimplex_obj v)⟩ = x := by
    have := ConcreteCategory.congr_hom (congr_app (sq.isPushout.inr_desc bT bV
      (Subcomplex.isInitialBot.hom_ext _ _)) (op ⦋0⦌)) ⟨v, Subcomplex.mem_ofSimplex_obj v⟩
    exact this.trans (const_app_zero x _)
  have hB : ∀ (m : ℕ) (σ : L _⦋m⦌), σ ∈ L.nonDegenerate m → σ ∉ Set.range (S.ι.app _) →
      ∃ y : (S : SSet.{u}) _⦋0⦌,
        S.ι.app _ y = L.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ (Z.vtx m)).op σ ∧
        Z.Good (g.app _ y) := by
    intro m σ hσ hσS
    have hT : σ ∉ T.obj (op ⦋m⦌) := fun h ↦ hσS ⟨⟨σ, Or.inl h⟩, rfl⟩
    refine ⟨⟨v, Or.inr (Subcomplex.mem_ofSimplex_obj v)⟩, (hL m σ hσ hT).symm, ?_⟩
    rw [hgV]
    exact hx
  obtain ⟨c, hc⟩ := exists_extension_of_mono_of_vertex S.ι g Z.Good Z.vtx Z.bvtx Z.bvtx_val
    Z.extend hB
  have hcT : T.ι ≫ c = bT := by
    rw [← Subcomplex.homOfLE_ι (le_sup_left : T ≤ S), Category.assoc, hc]
    exact sq.isPushout.inl_desc bT bV _
  have hcv : c.app _ v = x := by
    have e : c.app _ v = g.app _ ⟨v, Or.inr (Subcomplex.mem_ofSimplex_obj v)⟩ :=
      ConcreteCategory.congr_hom (congr_app hc (op ⦋0⦌))
        ⟨v, Or.inr (Subcomplex.mem_ofSimplex_obj v)⟩
    exact e.trans hgV
  have hle : Subcomplex.range (curry (CartesianMonoidalCategory.fst L (Δ[0] : SSet.{u}) ≫ c)) ≤
      Z.at v := by
    rintro ⟨k⟩ _ ⟨τ, rfl⟩
    refine Z.sub_full _ fun i ↦ (Z.mem_sub _).2 ?_
    have h1 := NatTrans.naturality_apply
      (curry (CartesianMonoidalCategory.fst L (Δ[0] : SSet.{u}) ≫ c) ≫ evalVertex v X)
      (SimplexCategory.const ⦋0⦌ k i).op τ
    have h2 : (curry (CartesianMonoidalCategory.fst L (Δ[0] : SSet.{u}) ≫ c) ≫
        evalVertex v X).app (op ⦋0⦌)
          (Δ[0].map (SimplexCategory.const ⦋0⦌ k i).op τ) = x := by
      rw [comp_evalVertex, uncurry_curry, ← Category.assoc, CartesianMonoidalCategory.lift_fst]
      exact (congrArg (c.app _) (const_app_zero v _)).trans hcv
    exact cast (congrArg Z.Good h1) (h2 ▸ hx)
  refine ⟨Subcomplex.lift _ hle, ?_⟩
  rw [Subcomplex.lift_ι_assoc]
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, ← Category.assoc,
    CartesianMonoidalCategory.whiskerRight_fst, Category.assoc, hcT, ← Category.assoc]
  convert Category.id_comp (uncurry b)
  exact CartesianMonoidalCategory.hom_ext _ _ (by simp) (stdSimplex.isTerminalObj₀.hom_ext _ _)

private instance isIso_pre_app {K M : SSet.{u}} (e : K ⟶ M) [IsIso e] (X : SSet.{u}) :
    IsIso ((pre e).app X) :=
  ⟨⟨(pre (inv e)).app X, by
    rw [← NatTrans.comp_app, ← pre_map, IsIso.inv_hom_id, pre_id]; rfl, by
    rw [← NatTrans.comp_app, ← pre_map, IsIso.hom_inv_id, pre_id]; rfl⟩⟩

private theorem trivialFibration_at {X : SSet.{u}} (Z : Side X) {K L : SSet.{u}} (i : K ⟶ L)
    [Mono i] (v : L _⦋0⦌) (hv : v ∉ Set.range (i.app _))
    (hL : ∀ (m : ℕ) (σ : L _⦋m⦌), σ ∈ L.nonDegenerate m → σ ∉ Set.range (i.app _) →
      L.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ (Z.vtx m)).op σ = v)
    (hX : ∃ x : X _⦋0⦌, Z.Good x) :
    modelCategoryQuillen.I.rlp ((Z.at v).ι ≫ (pre i).app X) := by
  have hfac : (pre i).app X = (pre (Subcomplex.range i).ι).app X ≫
      (pre (Subcomplex.toRange i)).app X := by
    rw [← NatTrans.comp_app, ← pre_map, Subfunctor.toRange_ι]
  rw [hfac, ← Category.assoc]
  refine MorphismProperty.comp_mem _ _ _ ?_ (MorphismProperty.of_isIso _ _)
  suffices H : ∀ n, HasLiftingProperty (boundary.{u} n).ι
      ((Z.at v).ι ≫ (pre (Subcomplex.range i).ι).app X) from
    fun _ _ _ ⟨n⟩ ↦ H n
  intro n
  refine ⟨fun {a b} sq ↦ ?_⟩
  cases n with
  | zero =>
    obtain ⟨l, hl⟩ := lift_zero_at Z (Subcomplex.range i) v hv hL hX b
    exact ⟨⟨⟨l, boundary.hom_ext₀, hl⟩⟩⟩
  | succ n =>
    obtain ⟨l, hl₁, hl₂⟩ := lift_succ_at Z (Subcomplex.range i) v hL n a b sq.w
    exact ⟨⟨⟨l, hl₁, hl₂⟩⟩⟩

private def Side.final (X : SSet.{u}) [X.Quasicategory] : Side X where
  vtx := Fin.last
  vtx_epi f := epi_apply_last f
  Good := IsFinal
  bvtx := boundary.lastVertex
  bvtx_val _ := rfl
  extend n b hb := (isFinal_iff_extend_boundary _).1 hb n b rfl
  sub := finalSubcomplex X
  mem_sub := mem_finalSubcomplex_obj_zero_iff
  sub_full _ h i := (mem_finalSubcomplex_obj_zero_iff _).1 (h i)

private def Side.initial (X : SSet.{u}) [X.Quasicategory] : Side X where
  vtx _ := 0
  vtx_epi f := epi_apply_zero f
  Good := IsInitialObject
  bvtx := boundary.firstVertex
  bvtx_val _ := rfl
  extend n b hb := (isInitialObject_iff_extend_boundary _).1 hb n b rfl
  sub := initialSubcomplex X
  mem_sub := mem_initialSubcomplex_obj_zero_iff
  sub_full _ h i := (mem_initialSubcomplex_obj_zero_iff _).1 (h i)

theorem trivialFibration_initialAtSubcomplex [X.Quasicategory] {K L : SSet.{u}} (i : K ⟶ L)
    [Mono i] (v : L _⦋0⦌) (hv : v ∉ Set.range (i.app _))
    (hL : ∀ (m : ℕ) (σ : L _⦋m⦌), σ ∈ L.nonDegenerate m → σ ∉ Set.range (i.app _) →
      L.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ 0).op σ = v)
    (hX : ∃ x : X _⦋0⦌, IsInitialObject x) :
    modelCategoryQuillen.I.rlp ((initialAtSubcomplex v X).ι ≫ (pre i).app X) :=
  trivialFibration_at (Side.initial X) i v hv hL hX

theorem trivialFibration_finalAtSubcomplex [X.Quasicategory] {K L : SSet.{u}} (i : K ⟶ L)
    [Mono i] (v : L _⦋0⦌) (hv : v ∉ Set.range (i.app _))
    (hL : ∀ (m : ℕ) (σ : L _⦋m⦌), σ ∈ L.nonDegenerate m → σ ∉ Set.range (i.app _) →
      L.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ (Fin.last m)).op σ = v)
    (hX : ∃ x : X _⦋0⦌, IsFinal x) :
    modelCategoryQuillen.I.rlp ((finalAtSubcomplex v X).ι ≫ (pre i).app X) :=
  trivialFibration_at (Side.final X) i v hv hL hX

private lemma horn_ι_app_apply {n : ℕ} (i j : Fin (n + 2)) (hij : j ≠ i) {m : ℕ}
    (y : (Δ[n] : SSet.{u}) _⦋m⦌) (t : Fin (m + 1)) :
    ((horn.ι.{u} i j hij).app (op ⦋m⦌) y).1 t = j.succAbove (y t) := by
  have := ConcreteCategory.congr_hom (congr_app (horn.ι_ι.{u} i j hij) (op ⦋m⦌)) y
  exact congrArg (fun z : (Δ[n + 1] : SSet.{u}) _⦋m⦌ => z t) this

private lemma mem_range_horn_ι {n : ℕ} (i j : Fin (n + 2)) (hij : j ≠ i) {m : ℕ}
    (σ : (Λ[n + 1, i] : SSet.{u}) _⦋m⦌) (h : ∀ t, σ.1 t ≠ j) :
    σ ∈ Set.range ((horn.ι.{u} i j hij).app (op ⦋m⦌)) := by
  have h1 : σ.1 ∈ (stdSimplex.face.{u} {j}ᶜ).obj (op ⦋m⦌) := by
    rw [stdSimplex.mem_face_iff]
    intro t
    simpa using h t
  rw [← stdSimplex.range_δ] at h1
  obtain ⟨y, hy⟩ := h1
  refine ⟨y, Subtype.ext ?_⟩
  exact (ConcreteCategory.congr_hom (congr_app (horn.ι_ι.{u} i j hij) (op ⦋m⦌)) y).trans hy

private lemma horn_vertex_eq {n : ℕ} {i : Fin (n + 1)} {m : ℕ} (σ : (Λ[n, i] : SSet.{u}) _⦋m⦌)
    (k : Fin (m + 1)) (w : (Λ[n, i] : SSet.{u}) _⦋0⦌) (h : σ.1 k = w.1 0) :
    (Λ[n, i] : SSet.{u}).map (SimplexCategory.const ⦋0⦌ ⦋m⦌ k).op σ = w := by
  refine Subtype.ext (stdSimplex.ext _ _ fun t ↦ ?_)
  obtain rfl : t = 0 := Fin.ext (by have := t.2; omega)
  exact h

private lemma horn₂₂_apply_zero {m : ℕ} (σ : (Λ[2, 2] : SSet.{u}) _⦋m⦌)
    (hσ : σ ∉ Set.range (horn₂₂.ι₀₂.{u}.app (op ⦋m⦌))) : σ.1 0 = 1 := by
  obtain ⟨t, ht⟩ : ∃ t, σ.1 t = 1 := by
    by_contra hcon
    exact hσ (mem_range_horn_ι 2 1 (by simp) σ fun t ht ↦ hcon ⟨t, ht⟩)
  obtain ⟨j, hj2, hjn⟩ := (mem_horn_iff_notMem_range σ.1 2).1 σ.2
  have h1 : σ.1 0 ≤ σ.1 t := (stdSimplex.asOrderHom σ.1).monotone (Fin.zero_le t)
  have h0 : σ.1 0 ≠ j := fun h ↦ hjn ⟨0, h⟩
  have h2 : σ.1 t ≠ j := fun h ↦ hjn ⟨t, h⟩
  rw [ht] at h1 h2
  revert hj2 h2 h0 h1
  generalize σ.1 0 = a
  generalize j = b
  revert a b
  decide

private lemma horn₂₀_apply_last {m : ℕ} (σ : (Λ[2, 0] : SSet.{u}) _⦋m⦌)
    (hσ : σ ∉ Set.range (horn₂₀.ι₀₁.{u}.app (op ⦋m⦌))) : σ.1 (Fin.last m) = 2 := by
  obtain ⟨t, ht⟩ : ∃ t, σ.1 t = 2 := by
    by_contra hcon
    exact hσ (mem_range_horn_ι 0 2 (by simp) σ fun t ht ↦ hcon ⟨t, ht⟩)
  have h1 : σ.1 t ≤ σ.1 (Fin.last m) := (stdSimplex.asOrderHom σ.1).monotone (Fin.le_last t)
  rw [ht] at h1
  revert h1
  generalize σ.1 (Fin.last m) = a
  revert a
  decide

theorem trivialFibration_cospan_initialAt [X.Quasicategory]
    (hX : ∃ x : X _⦋0⦌, IsInitialObject x) :
    modelCategoryQuillen.I.rlp
      ((initialAtSubcomplex (horn₂₂.ι₁₂.app _ (stdSimplex.obj₀Equiv.symm 0)) X).ι ≫
        (pre horn₂₂.ι₀₂).app X) := by
  have : Mono horn₂₂.ι₀₂.{u} := mono_of_mono_fac (horn.ι_ι.{u} 2 1 (by simp))
  have hv1 : (horn₂₂.ι₁₂.{u}.app _ (stdSimplex.obj₀Equiv.symm 0)).1 0 = 1 := by
    rw [horn_ι_app_apply]
    rfl
  refine trivialFibration_initialAtSubcomplex _ _ ?_ (fun m σ _ hσ ↦ ?_) hX
  · rintro ⟨y, hy⟩
    have := congrArg (fun z ↦ z.1 0) hy
    simp only at this
    rw [horn_ι_app_apply, hv1] at this
    exact Fin.succAbove_ne _ _ this
  · exact horn_vertex_eq σ 0 _ (hv1 ▸ horn₂₂_apply_zero σ hσ)

theorem trivialFibration_span_finalAt [X.Quasicategory] (hX : ∃ x : X _⦋0⦌, IsFinal x) :
    modelCategoryQuillen.I.rlp
      ((finalAtSubcomplex (horn₂₀.ι₀₂.app _ (stdSimplex.obj₀Equiv.symm 1)) X).ι ≫
        (pre horn₂₀.ι₀₁).app X) := by
  have : Mono horn₂₀.ι₀₁.{u} := mono_of_mono_fac (horn.ι_ι.{u} 0 2 (by simp))
  have hv1 : (horn₂₀.ι₀₂.{u}.app _ (stdSimplex.obj₀Equiv.symm 1)).1 0 = 2 := by
    rw [horn_ι_app_apply]
    rfl
  refine trivialFibration_finalAtSubcomplex _ _ ?_ (fun m σ _ hσ ↦ ?_) hX
  · rintro ⟨y, hy⟩
    have := congrArg (fun z ↦ z.1 0) hy
    simp only at this
    rw [horn_ι_app_apply, hv1] at this
    exact Fin.succAbove_ne _ _ this
  · exact horn_vertex_eq σ _ _ ((horn₂₀_apply_last σ hσ).trans hv1.symm)

end SSet
