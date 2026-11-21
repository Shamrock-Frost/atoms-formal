import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.FullSubcomplex
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianFibration
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianPrism
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.MappingSpace
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne

universe u

open CategoryTheory Limits Simplicial MonoidalCategory MonoidalClosed
  CartesianMonoidalCategory Opposite HomotopicalAlgebra

namespace SSet

private lemma simplexMap_ext {m n : ℕ} {f g : (Δ[m] : SSet.{u}) ⟶ Δ[n]}
    (h : ∀ i, yonedaEquiv f i = yonedaEquiv g i) : f = g :=
  yonedaEquiv.injective (stdSimplex.ext _ _ h)

private lemma lift_id_comp_uncurry_eq_ihomPointEquiv {X : SSet.{u}} (g : Δ[1] ⟶ (ihom Δ[1]).obj X)
    (i : Fin 2) :
    lift (𝟙 Δ[1]) (stdSimplex.isTerminalObj₀.from Δ[1] ≫ stdSimplex.δ i) ≫
      uncurry g = ihomPointEquiv Δ[1] X (stdSimplex.δ i ≫ g) := by
  rw [ihomPointEquiv_apply, uncurry_natural_left, ← Category.assoc,
    lift_whiskerLeft]

theorem isCartesianEdge_of_invStruct_ihom {X S : SSet.{u}}
    [X.Quasicategory] [S.Quasicategory] (p : X ⟶ S) [InnerFibration p]
    {e e' : ((ihom Δ[1]).obj X) _⦋0⦌} (α : Edge e e')
    (hα : Nonempty α.InvStruct)
    (he : IsCartesianEdge p (ihomPointEquiv Δ[1] X (yonedaEquiv.symm e))) :
    IsCartesianEdge p (ihomPointEquiv Δ[1] X (yonedaEquiv.symm e')) := by
  classical
  let I := hα.some.invStructInv
  let β := hα.some.inv
  let g : Δ[1] ⟶ (ihom Δ[1]).obj X := yonedaEquiv.symm β.edge
  let H := uncurry g
  have h0 : stdSimplex.δ 1 ≫ g = yonedaEquiv.symm e' := by
    dsimp only [g]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, β.src_eq]
  have h1 : stdSimplex.δ 0 ≫ g = yonedaEquiv.symm e := by
    dsimp only [g]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, β.tgt_eq]
  have hc (i : Fin 2) : stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ i) =
      stdSimplex.isTerminalObj₀.from Δ[1] ≫ yonedaEquiv.symm
        (stdSimplex.obj₀Equiv.symm i) := by
    apply simplexMap_ext
    intro j
    fin_cases i <;> fin_cases j <;> rfl
  have hv (i : Fin 2) : IsCartesianEdge p
      (lift (stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ i)) (𝟙 Δ[1]) ≫ H) := by
    rw [hc]
    change IsCartesianEdge p
      (lift (stdSimplex.isTerminalObj₀.from Δ[1] ≫ yonedaEquiv.symm
        (stdSimplex.obj₀Equiv.symm i)) (𝟙 Δ[1]) ≫ uncurry g)
    rw [← comp_evalVertex]
    apply isCartesianEdge_of_invStruct p
    exact ⟨(I.map (evalVertex (stdSimplex.obj₀Equiv.symm i) X)).ofEq
      (by simp only [g, yonedaEquiv_comp]; rfl)⟩
  have hu : IsCartesianEdge p (stdSimplex.δ 0 ≫ prodStdSimplex.upperTriangle ≫ H) := by
    rw [← Category.assoc, prodStdSimplex.δ_zero_upperTriangle,
      hc 1]
    have hc1 : yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        (stdSimplex.δ 0 : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
      rw [yonedaEquiv_symm_zero, stdSimplex.δ_zero_eq_const]
    rw [hc1, lift_id_comp_uncurry_eq_ihomPointEquiv, h1]
    exact he
  have hd := (isCartesianEdge_δ_two_iff_δ_one p (prodStdSimplex.upperTriangle ≫ H) hu).1
    (by simpa only [← Category.assoc, prodStdSimplex.δ_two_upperTriangle] using hv 0)
  have hl : IsCartesianEdge p (stdSimplex.δ 0 ≫ prodStdSimplex.lowerTriangle ≫ H) := by
    simpa only [← Category.assoc, prodStdSimplex.δ_zero_lowerTriangle] using hv 1
  have he' := (isCartesianEdge_δ_two_iff_δ_one p (prodStdSimplex.lowerTriangle ≫ H) hl).2
    (by simpa only [← Category.assoc, prodStdSimplex.δ_one_lowerTriangle,
      prodStdSimplex.δ_one_upperTriangle] using hd)
  rw [← Category.assoc, prodStdSimplex.δ_two_lowerTriangle, hc 0] at he'
  have hc0 : yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (stdSimplex.δ 1 : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
    rw [yonedaEquiv_symm_zero, stdSimplex.δ_one_eq_const]
  rwa [hc0, lift_id_comp_uncurry_eq_ihomPointEquiv, h0] at he'

private lemma range_le_full {Z : SSet.{u}} (P : Z _⦋0⦌ → Prop) {n : ℕ}
    (a : Δ[n] ⟶ Z) : Subcomplex.range a ≤ Z.fullSubcomplex P ↔
      ∀ i, P (a.app _ (stdSimplex.obj₀Equiv.symm i)) := by
  rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff]
  exact forall_congr' fun i ↦ by
    rw [show Z.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op (yonedaEquiv a) =
      a.app _ (stdSimplex.obj₀Equiv.symm i) from (a.naturality_apply _ _).symm.trans rfl]

private lemma hasLift_boundary_of_unionProd {X S : SSet.{u}} (p : X ⟶ S) (n : ℕ)
    (a : (∂Δ[n + 1] : SSet.{u}) ⟶ (ihom Δ[1]).obj X)
    (b : Δ[n + 1] ⟶ (Functor.PullbackObjObj.ofHasPullback internalHom
      (stdSimplex.δ (0 : Fin 2)) p).pt)
    (sq : CommSq a (boundary (n + 1)).ι
      (Functor.PullbackObjObj.ofHasPullback internalHom (stdSimplex.δ (0 : Fin 2)) p).π b)
    (h : (((Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd
      (boundary (n + 1))) : SSet.{u}) ⟶ X)
    (ht : (Subcomplex.unionProd.pushoutObjObj (Λ[1, 1]) (boundary (n + 1))).inl ≫ h =
      uncurry a)
    (hs : (Subcomplex.unionProd.pushoutObjObj (Λ[1, 1]) (boundary (n + 1))).inr ≫ h =
      stdSimplex.isTerminalObj₀.from (Λ[1, 1] : SSet.{u}) ▷ Δ[n + 1] ≫
        uncurry (b ≫ (Functor.PullbackObjObj.ofHasPullback internalHom
          (stdSimplex.δ (0 : Fin 2)) p).fst))
    (sq' : CommSq h ((Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).unionProd
      (boundary (n + 1))).ι p (uncurry (b ≫
        (Functor.PullbackObjObj.ofHasPullback internalHom (stdSimplex.δ (0 : Fin 2)) p).snd)))
    (hLift : sq'.HasLift) : sq.HasLift := by
  let K := (Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex)
  let T := boundary.{u} (n + 1)
  let pb := Functor.PullbackObjObj.ofHasPullback internalHom (stdSimplex.δ (0 : Fin 2)) p
  let po := Subcomplex.unionProd.pushoutObjObj K T
  let s := uncurry (b ≫ pb.fst)
  let endpoint := stdSimplex.isTerminalObj₀.from (K : SSet.{u})
  obtain ⟨L⟩ := hLift.exists_lift
  refine ⟨⟨⟨curry L.l, ?_, ?_⟩⟩⟩
  · apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    exact ((po.inl_ι_assoc L.l).symm.trans
      ((congrArg (po.inl ≫ ·) L.fac_left).trans ht))
  · apply pb.isPullback.hom_ext
    · erw [Category.assoc, pb.π_fst]
      dsimp only [internalHom]
      rw [curry_pre_app]
      apply uncurry_injective
      rw [uncurry_curry]
      have he := congrArg (po.inr ≫ ·) L.fac_left
      rw [hs] at he
      have he' : endpoint ▷ Δ[n + 1] ≫ stdSimplex.δ (0 : Fin 2) ▷ Δ[n + 1] ≫ L.l =
          endpoint ▷ Δ[n + 1] ≫ s := by
        have hk : endpoint ▷ Δ[n + 1] ≫ stdSimplex.δ (0 : Fin 2) ▷ Δ[n + 1] =
            po.inr ≫ (K.unionProd T).ι :=
          (comp_whiskerRight endpoint (stdSimplex.δ (0 : Fin 2)) Δ[n + 1]).symm.trans
            ((congrArg (· ▷ Δ[n + 1]) horn_one_one_ι).trans po.inr_ι.symm)
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ L.l) hk).trans ((Category.assoc _ _ _).trans he))
      let endpointSection := horn.ι 1 0 (by decide : (0 : Fin 2) ≠ 1)
      have hsection : endpointSection ≫ endpoint = 𝟙 _ := stdSimplex.isTerminalObj₀.hom_ext _ _
      have he'' := congrArg (fun t ↦ endpointSection ▷ Δ[n + 1] ≫ t) he'
      change stdSimplex.δ (0 : Fin 2) ▷ Δ[n + 1] ≫ L.l = s
      simpa only [← Category.assoc, ← comp_whiskerRight, hsection,
        id_whiskerRight, Category.id_comp] using he''
    · erw [Category.assoc, pb.π_snd]
      dsimp only [internalHom]
      rw [← curry_natural_right, L.fac_right]
      exact curry_uncurry _

private lemma hasLift_boundary_cartesianArrow_π {X S : SSet.{u}} (p : X ⟶ S)
    [IsCartesianFibration p] (n : ℕ)
    (a : (∂Δ[n + 1] : SSet.{u}) ⟶ (ihom Δ[1]).obj X)
    (b : Δ[n + 1] ⟶ (Functor.PullbackObjObj.ofHasPullback internalHom
      (stdSimplex.δ (0 : Fin 2)) p).pt)
    (sq : CommSq a (boundary (n + 1)).ι
      (Functor.PullbackObjObj.ofHasPullback internalHom (stdSimplex.δ (0 : Fin 2)) p).π b)
    (ha : ∀ z : (∂Δ[n + 1] : SSet.{u}) _⦋0⦌,
      IsCartesianEdge p (ihomPointEquiv Δ[1] X (yonedaEquiv.symm (a.app _ z)))) :
    sq.HasLift := by
  let K := (Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex)
  let T := boundary.{u} (n + 1)
  let pb := Functor.PullbackObjObj.ofHasPullback internalHom (stdSimplex.δ (0 : Fin 2)) p
  let po := Subcomplex.unionProd.pushoutObjObj K T
  let t := uncurry a
  let s := uncurry (b ≫ pb.fst)
  let v := uncurry (b ≫ pb.snd)
  have hf : stdSimplex.δ (0 : Fin 2) ▷ (T : SSet.{u}) ≫ t = Δ[0] ◁ T.ι ≫ s := by
    have h : a ≫ (pre (stdSimplex.δ (0 : Fin 2))).app X = T.ι ≫ (b ≫ pb.fst) :=
      (congrArg (a ≫ ·) pb.π_fst.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ pb.fst) sq.w).trans (Category.assoc _ _ _)))
    exact (uncurry_pre_app X a (stdSimplex.δ (0 : Fin 2))).symm.trans
      ((congrArg uncurry h).trans (uncurry_natural_left T.ι (b ≫ pb.fst)))
  have ht : t ≫ p = Δ[1] ◁ T.ι ≫ v := by
    have h : a ≫ (ihom Δ[1]).map p = T.ι ≫ (b ≫ pb.snd) :=
      (congrArg (a ≫ ·) pb.π_snd.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ pb.snd) sq.w).trans (Category.assoc _ _ _)))
    exact (uncurry_natural_right a p).symm.trans
      ((congrArg uncurry h).trans (uncurry_natural_left T.ι (b ≫ pb.snd)))
  have hs : s ≫ p = stdSimplex.δ (0 : Fin 2) ▷ Δ[n + 1] ≫ v := by
    have h : (b ≫ pb.fst) ≫ (ihom Δ[0]).map p =
        (b ≫ pb.snd) ≫ (pre (stdSimplex.δ (0 : Fin 2))).app S :=
      (Category.assoc _ _ _).trans
        ((congrArg (b ≫ ·) pb.isPullback.w).trans (Category.assoc _ _ _).symm)
    exact (uncurry_natural_right (b ≫ pb.fst) p).symm.trans
      ((congrArg uncurry h).trans (uncurry_pre_app S (b ≫ pb.snd) (stdSimplex.δ (0 : Fin 2))))
  let endpoint := stdSimplex.isTerminalObj₀.from (K : SSet.{u})
  have hw : K.ι ▷ (T : SSet.{u}) ≫ t = (K : SSet.{u}) ◁ T.ι ≫ endpoint ▷ Δ[n + 1] ≫ s := by
    rw [← horn_one_one_ι, comp_whiskerRight, Category.assoc, hf,
      ← whisker_exchange_assoc]
  let h := po.isPushout.desc t (endpoint ▷ Δ[n + 1] ≫ s) hw
  have wh : h ≫ p = (K.unionProd T).ι ≫ v := by
    apply po.isPushout.hom_ext
    · erw [← Category.assoc, po.isPushout.inl_desc, ht,
        ← Category.assoc]
    · erw [← Category.assoc, po.isPushout.inr_desc, Category.assoc, hs,
        ← Category.assoc, ← comp_whiskerRight, horn_one_one_ι,
        ← Category.assoc]
  let z : (T : SSet.{u}) _⦋0⦌ :=
    ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)), by
      rw [boundary_obj_eq_univ 0 (n + 1)]; trivial⟩
  have hz : prismLastEdge n =
      lift (𝟙 Δ[1]) (stdSimplex.isTerminalObj₀.from Δ[1] ≫ yonedaEquiv.symm z) ≫ po.inl := by
    apply (cancel_mono (K.unionProd T).ι).1
    erw [Category.assoc, po.inl_ι, prismLastEdge, Subcomplex.lift_ι]
  have hh : IsCartesianEdge p (prismLastEdge n ≫ h) := by
    erw [hz, Category.assoc, po.isPushout.inl_desc]
    change IsCartesianEdge p (_ ≫ uncurry a)
    have he := ha z
    rw [← yonedaEquiv_symm_comp, ihomPointEquiv_apply, uncurry_natural_left,
      ← Category.assoc, lift_whiskerLeft] at he
    exact he
  let sq' : CommSq h (K.unionProd T).ι p v := ⟨wh⟩
  have hLift := IsCartesianEdge.hasLift_unionProd p hh n h v sq' rfl
  exact hasLift_boundary_of_unionProd p n a b sq h (po.isPushout.inl_desc _ _ _)
    (po.isPushout.inr_desc _ _ _) sq' hLift

theorem rlp_I_cartesianArrows {Z S : SSet.{u}} (p : Z ⟶ S) [IsCartesianFibration p] :
    modelCategoryQuillen.I.rlp
      ((((ihom Δ[1]).obj Z).fullSubcomplex
        (fun e ↦ IsCartesianEdge p (ihomPointEquiv Δ[1] Z (yonedaEquiv.symm e)))).ι ≫
        (Functor.PullbackObjObj.ofHasPullback internalHom (stdSimplex.δ (0 : Fin 2)) p).π) := by
  rintro A B j ⟨n⟩
  let P := fun e ↦ IsCartesianEdge p (ihomPointEquiv Δ[1] Z (yonedaEquiv.symm e))
  let C := ((ihom Δ[1]).obj Z).fullSubcomplex P
  let pb := Functor.PullbackObjObj.ofHasPullback internalHom (stdSimplex.δ (0 : Fin 2)) p
  refine ⟨fun {a b} sq ↦ ?_⟩
  cases n with
  | zero =>
    let y := ihomPointEquiv Δ[0] Z (b ≫ pb.fst)
    let f := ihomPointEquiv Δ[1] S (b ≫ pb.snd)
    have hf : stdSimplex.δ 0 ≫ f = y ≫ p := by
      have h : (b ≫ pb.fst) ≫ (ihom Δ[0]).map p =
          (b ≫ pb.snd) ≫ (pre (stdSimplex.δ (0 : Fin 2))).app S :=
        (Category.assoc _ _ _).trans
          ((congrArg (b ≫ ·) pb.isPullback.w).trans (Category.assoc _ _ _).symm)
      exact (ihomPointEquiv_comp_pre_app (b ≫ pb.snd) (stdSimplex.δ (0 : Fin 2))).symm.trans
        ((congrArg (ihomPointEquiv Δ[0] S) h.symm).trans
          (ihomPointEquiv_comp_ihom_map (b ≫ pb.fst) p))
    obtain ⟨f', hfp, hfy, hfc⟩ := IsCartesianFibration.exists_isCartesianEdge (p := p)
      (yonedaEquiv y) f (by
        simpa only [← yonedaEquiv_comp, Equiv.symm_apply_apply] using hf)
    rw [Equiv.symm_apply_apply] at hfy
    let l := (ihomPointEquiv Δ[1] Z).symm f'
    have hl : Subcomplex.range l ≤ C := by
      rw [range_le_full]
      intro i
      fin_cases i
      change P (yonedaEquiv l)
      dsimp only [P]
      rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
      exact hfc
    refine ⟨⟨⟨Subcomplex.lift l hl, (by
      have hi : IsInitial (∂Δ[0] : SSet.{u}) := by
        rw [boundary_zero]; exact Subcomplex.isInitialBot
      exact hi.hom_ext _ _), ?_⟩⟩⟩
    erw [← Category.assoc, Subcomplex.lift_ι]
    apply pb.isPullback.hom_ext
    · erw [Category.assoc, pb.π_fst]
      dsimp only [internalHom]
      apply (ihomPointEquiv Δ[0] Z).injective
      rw [ihomPointEquiv_comp_pre_app, Equiv.apply_symm_apply]
      exact hfy
    · erw [Category.assoc, pb.π_snd]
      dsimp only [internalHom]
      apply (ihomPointEquiv Δ[1] S).injective
      rw [ihomPointEquiv_comp_ihom_map, Equiv.apply_symm_apply, hfp]
  | succ n =>
    let sq' : CommSq (a ≫ C.ι) (boundary (n + 1)).ι pb.π b := ⟨by
      exact (Category.assoc a C.ι pb.π).trans sq.w⟩
    have hLift := hasLift_boundary_cartesianArrow_π p n (a ≫ C.ι) b sq' (fun z ↦
      (mem_fullSubcomplex_obj_zero_iff P _).1 (a.app _ z).property)
    obtain ⟨L⟩ := hLift.exists_lift
    have hl : Subcomplex.range L.l ≤ C := by
      rw [range_le_full]
      intro i
      let z : (∂Δ[n + 1] : SSet.{u}) _⦋0⦌ :=
        ⟨stdSimplex.obj₀Equiv.symm i, by rw [boundary_obj_eq_univ 0 (n + 1)]; trivial⟩
      have he := congrArg (fun t ↦ t.app (op ⦋0⦌) z) L.fac_left
      change L.l.app _ (stdSimplex.obj₀Equiv.symm i) = (a.app _ z).val at he
      rw [he]
      exact (mem_fullSubcomplex_obj_zero_iff P _).1 (a.app _ z).property
    refine ⟨⟨⟨Subcomplex.lift L.l hl, ?_, ?_⟩⟩⟩
    · apply (cancel_mono C.ι).1
      rw [Category.assoc, Subcomplex.lift_ι]
      exact L.fac_left
    · erw [← Category.assoc, Subcomplex.lift_ι]
      exact L.fac_right

end SSet
