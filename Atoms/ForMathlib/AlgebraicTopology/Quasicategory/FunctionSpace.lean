import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.Isofibration
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty Opposite
  MonoidalCategory

universe w v u

namespace SSet

section CellLifting

open HasLiftingProperty.transfiniteComposition in
private lemma hasLift_of_forall_sqStruct {C : Type u} [Category.{v} C] {J : Type w}
    [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J] {F : J ⥤ C}
    [F.IsWellOrderContinuous] {c : Cocone F} (hc : IsColimit c) {X Y : C} {p : X ⟶ Y}
    {f : F.obj ⊥ ⟶ X} {g : c.pt ⟶ Y}
    (hF : ∀ (j : J) (_ : ¬IsMax j) (sq' : SqStruct c p f g j), sq'.sq.HasLift)
    (sq : CommSq f (c.ι.app ⊥) p g) : sq.HasLift := by
  let d : (sqFunctor c p f g).WellOrderInductionData := .ofExists
    (fun j hj sq' ↦ by
      obtain ⟨l⟩ := (hF j hj sq').exists_lift
      refine ⟨{ f' := l.l, w₁ := ?_, w₂ := l.fac_right }, SqStruct.ext l.fac_left⟩
      exact (congrArg (· ≫ l.l) (F.map_comp (homOfLE bot_le)
        (homOfLE (Order.le_succ j)))).trans ((Category.assoc _ _ _).trans
          ((congrArg _ l.fac_left).trans sq'.w₁)))
    (fun j hj s ↦ ⟨wellOrderInductionData.lift hj s, fun i hij ↦
      wellOrderInductionData.map_lift hj s hij⟩)
  obtain ⟨s, hs⟩ := d.surjective { w₂ := sq.w, .. }
  replace hs := congr_arg SqStruct.f' hs
  dsimp at hs
  let t : Cocone F := Cocone.mk X
    { app j := (s.1 ⟨j⟩).f'
      naturality j j' g := (congr_arg SqStruct.f' (s.2 g.op)).trans (Category.comp_id _).symm }
  refine ⟨⟨{ l := hc.desc t, fac_left := ?_, fac_right := hc.hom_ext fun j ↦ ?_ }⟩⟩
  · rw [hc.fac t ⊥]
    exact hs
  · rw [reassoc_of% (hc.fac t j)]
    exact (s.1 ⟨j⟩).w₂

private lemma hasLift_of_attachCells {C : Type u} [Category.{v} C] {α : Type*} {A B : α → C}
    {g : ∀ a, A a ⟶ B a} {X₁ X₂ X Y : C} {f : X₁ ⟶ X₂} (c : AttachCells.{w} g f)
    {p : X ⟶ Y} {u : X₁ ⟶ X} {w : X₂ ⟶ Y} (sq : CommSq u f p w)
    (h : ∀ (k : c.ι) (sqk : CommSq (c.cofan₁.inj k ≫ c.g₁ ≫ u) (g (c.π k)) p (c.cell k ≫ w)),
      sqk.HasLift) : sq.HasLift := by
  have sqk (k : c.ι) : CommSq (c.cofan₁.inj k ≫ c.g₁ ≫ u) (g (c.π k)) p (c.cell k ≫ w) := ⟨by
    rw [Category.assoc, Category.assoc, sq.w, c.isPushout.w_assoc, c.hm_assoc, c.cell_def,
      Category.assoc]⟩
  let l (k : c.ι) := ((h k (sqk k)).exists_lift.some)
  let d : c.cofan₂.pt ⟶ X := Cofan.IsColimit.desc c.isColimit₂ fun k ↦ (l k).l
  have hd : c.g₁ ≫ u = c.m ≫ d := Cofan.IsColimit.hom_ext c.isColimit₁ _ _ fun k ↦ by
    rw [c.hm_assoc, Cofan.IsColimit.fac, (l k).fac_left]
  refine ⟨⟨⟨c.isPushout.desc u d hd, c.isPushout.inl_desc _ _ _, ?_⟩⟩⟩
  refine c.isPushout.hom_ext ?_ ?_
  · rw [c.isPushout.inl_desc_assoc, sq.w]
  · refine Cofan.IsColimit.hom_ext c.isColimit₂ _ _ fun k ↦ ?_
    rw [c.isPushout.inr_desc_assoc, Cofan.IsColimit.fac_assoc, (l k).fac_right, c.cell_def,
      Category.assoc]

private def isInitialBoundaryZero : IsInitial (∂Δ[0] : SSet.{u}) := by
  rw [boundary_zero]
  exact Subcomplex.isInitialBot

theorem hasLift_of_mono_of_cell {K L X Y : SSet.{u}} (i : K ⟶ L) [Mono i] {p : X ⟶ Y}
    {u : K ⟶ X} {w : L ⟶ Y} (sq : CommSq u i p w)
    (h : ∀ (d : ℕ) (σ : L _⦋d⦌), σ ∈ L.nonDegenerate d → σ ∉ Set.range (i.app _) →
      ∀ (a : (∂Δ[d] : SSet.{u}) ⟶ X) (hsq : CommSq a ∂Δ[d].ι p (yonedaEquiv.symm σ ≫ w)),
        (∀ (m : ℕ) (y : (∂Δ[d] : SSet.{u}) _⦋m⦌) (x : K _⦋m⦌),
          i.app _ x = (yonedaEquiv.symm σ).app _ y.1 → a.app _ y = u.app _ x) →
        hsq.HasLift) :
    sq.HasLift := by
  let K' := relativeCellComplexOfMono i
  have hfac : K'.isoBot.hom ≫ i = K'.incl.app ⊥ := ((Iso.inv_comp_eq _).1 K'.fac).symm
  have sq₀ : CommSq (K'.isoBot.hom ≫ u) (K'.incl.app ⊥) p w :=
    ⟨by rw [Category.assoc, sq.w, ← Category.assoc, hfac]⟩
  have key (j : ℕ) (hj : ¬IsMax j) (sq' : HasLiftingProperty.transfiniteComposition.SqStruct
      (Cocone.mk L K'.incl) p (K'.isoBot.hom ≫ u) w j) : sq'.sq.HasLift := by
    refine hasLift_of_attachCells (K'.attachCells j hj) sq'.sq fun k sqk ↦ ?_
    have hk : (K'.attachCells j hj).cell k ≫ K'.incl.app (Order.succ j) =
        yonedaEquiv.symm k.simplex := relativeCellComplexOfMono.Cell.ι_b_ι k
    have hw : (K'.attachCells j hj).cell k ≫ K'.incl.app (Order.succ j) ≫ w =
        yonedaEquiv.symm k.simplex ≫ w := by rw [← hk, Category.assoc]
    have sqk' : CommSq ((K'.attachCells j hj).cofan₁.inj k ≫ (K'.attachCells j hj).g₁ ≫ sq'.f')
        ∂Δ[j].ι p (yonedaEquiv.symm k.simplex ≫ w) := ⟨sqk.w.trans (congrArg (∂Δ[j].ι ≫ ·) hw)⟩
    suffices H : sqk'.HasLift by
      obtain ⟨l⟩ := H.exists_lift
      exact ⟨⟨⟨l.l, l.fac_left, l.fac_right.trans hw.symm⟩⟩⟩
    refine h j k.simplex k.nonDegenerate k.notMem _ sqk' fun m y x hx ↦ ?_
    have hy : ((K'.attachCells j hj).cofan₁.inj k ≫ (K'.attachCells j hj).g₁).app _ y =
        (K'.F.map (homOfLE bot_le)).app _ (K'.isoBot.inv.app _ x) := by
      apply Subtype.ext
      have e₁ := ConcreteCategory.congr_hom
        (congr_app (relativeCellComplexOfMono.Cell.ι_t_ι_eq_ι_l_b_ι k) _) y
      have e₂ := ConcreteCategory.congr_hom
        (congr_app (relativeCellComplexOfMono.Cell.ι_b_ι k) _) y.1
      have e₃ := ConcreteCategory.congr_hom (congr_app K'.fac _) x
      exact e₁.trans (e₂.trans (hx.symm.trans e₃.symm))
    have h₁ := ConcreteCategory.congr_hom (congr_app sq'.w₁ _) (K'.isoBot.inv.app _ x)
    have h₂ := ConcreteCategory.congr_hom (congr_app K'.isoBot.inv_hom_id _) x
    exact (congrArg (sq'.f'.app _) hy).trans (h₁.trans (congrArg (u.app _) h₂))
  obtain ⟨l⟩ := (hasLift_of_forall_sqStruct K'.isColimit key sq₀).exists_lift
  refine ⟨⟨⟨l.l, ?_, l.fac_right⟩⟩⟩
  calc i ≫ l.l = (K'.isoBot.inv ≫ K'.incl.app ⊥) ≫ l.l := by rw [K'.fac]
    _ = u := by rw [Category.assoc, l.fac_left, Iso.inv_hom_id_assoc]

theorem hasLift_of_mono {K L X Y : SSet.{u}} (i : K ⟶ L) [Mono i] {p : X ⟶ Y}
    (hp : ∀ n : ℕ, HasLiftingProperty (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι p)
    {u : K ⟶ X} {w : L ⟶ Y} (sq : CommSq u i p w)
    (h₀ : ∀ y : L _⦋0⦌, y ∉ Set.range (i.app _) →
      ∃ x : Δ[0] ⟶ X, x ≫ p = yonedaEquiv.symm y ≫ w) : sq.HasLift :=
  hasLift_of_mono_of_cell i sq fun d σ _ hσ _ hsq _ ↦ by
    cases d with
    | zero =>
      obtain ⟨x, hx⟩ := h₀ σ hσ
      exact ⟨⟨⟨x, isInitialBoundaryZero.hom_ext _ _, hx⟩⟩⟩
    | succ n => exact (hp n).sq_hasLift hsq

def boundary.firstVertex (n : ℕ) : (∂Δ[n + 1] : SSet.{u}) _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm 0, by rw [boundary_obj_eq_univ 0 (n + 1)]; trivial⟩

theorem exists_extension_of_mono_of_vertex {A B X : SSet.{u}} (j : A ⟶ B) [Mono j]
    (a : A ⟶ X) (P : X _⦋0⦌ → Prop) (k : ∀ m : ℕ, Fin (m + 1))
    (y : ∀ n : ℕ, (∂Δ[n + 1] : SSet.{u}) _⦋0⦌)
    (hy : ∀ n : ℕ, (y n).1 = stdSimplex.obj₀Equiv.symm (k (n + 1)))
    (hP : ∀ (n : ℕ) (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X), P (b.app _ (y n)) →
      ∃ c : Δ[n + 1] ⟶ X, (∂Δ[n + 1]).ι ≫ c = b)
    (hB : ∀ (m : ℕ) (σ : B _⦋m⦌), σ ∈ B.nonDegenerate m → σ ∉ Set.range (j.app _) →
      ∃ x : A _⦋0⦌, j.app _ x = B.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ (k m)).op σ ∧
        P (a.app _ x)) :
    ∃ c : B ⟶ X, j ≫ c = a := by
  have sq : CommSq a j (stdSimplex.isTerminalObj₀.from X) (stdSimplex.isTerminalObj₀.from B) :=
    ⟨stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  suffices H : sq.HasLift from ⟨H.exists_lift.some.l, H.exists_lift.some.fac_left⟩
  refine hasLift_of_mono_of_cell j sq fun d σ hσ hσ' b hsq hb ↦ ?_
  obtain ⟨x, hx, hPx⟩ := hB d σ hσ hσ'
  cases d with
  | zero =>
    refine (hσ' ⟨x, hx.trans ?_⟩).elim
    rw [SimplexCategory.hom_zero_zero (SimplexCategory.const ⦋0⦌ ⦋0⦌ (k 0)), op_id,
      Functor.map_id_apply]
  | succ n =>
    have hbx : b.app _ (y n) = a.app _ x := hb 0 (y n) x (hx.trans (by
      rw [hy, ← yonedaEquiv_symm_app_objEquiv_symm]
      rfl))
    obtain ⟨c, hc⟩ := hP n b (hbx ▸ hPx)
    exact ⟨⟨⟨c, hc, stdSimplex.isTerminalObj₀.hom_ext _ _⟩⟩⟩

theorem exists_extension_of_mono_of_firstVertex {A B X : SSet.{u}} (j : A ⟶ B) [Mono j]
    (a : A ⟶ X) (P : X _⦋0⦌ → Prop)
    (hP : ∀ (n : ℕ) (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X), P (b.app _ (boundary.firstVertex n)) →
      ∃ c : Δ[n + 1] ⟶ X, (∂Δ[n + 1]).ι ≫ c = b)
    (hB : ∀ (m : ℕ) (σ : B _⦋m⦌), σ ∈ B.nonDegenerate m → σ ∉ Set.range (j.app _) →
      ∃ x : A _⦋0⦌, j.app _ x = B.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ 0).op σ ∧
        P (a.app _ x)) :
    ∃ c : B ⟶ X, j ≫ c = a :=
  exists_extension_of_mono_of_vertex j a P (fun _ ↦ 0) boundary.firstVertex (fun _ ↦ rfl) hP hB

private lemma hasLift_of_pairing {Z : SSet.{u}} {A : Z.Subcomplex} (P : A.Pairing)
    [P.IsRegular] {X Y : SSet.{u}} {p : X ⟶ Y} {u : (A : SSet.{u}) ⟶ X} {w : Z ⟶ Y}
    (sq : CommSq u A.ι p w)
    (h : ∀ (x : P.II)
      (a : (horn (x.1.dim + 1) ((P.isUniquelyCodimOneFace x).index rfl) : SSet.{u}) ⟶ X)
      (hab : CommSq a (horn (x.1.dim + 1) ((P.isUniquelyCodimOneFace x).index rfl)).ι p
        (yonedaEquiv.symm ((P.p x).val.cast (P.isUniquelyCodimOneFace x).dim_eq).simplex ≫ w)),
      (∀ (k : ℕ) (y : (horn (x.1.dim + 1) ((P.isUniquelyCodimOneFace x).index rfl) :
          SSet.{u}) _⦋k⦌)
        (hy : (yonedaEquiv.symm ((P.p x).val.cast (P.isUniquelyCodimOneFace x).dim_eq).simplex).app
          _ y.1 ∈ A.obj _),
        a.app _ y = u.app _ ⟨_, hy⟩) → hab.HasLift) :
    sq.HasLift := by
  let K := P.rankFunction.relativeCellComplex
  have hfac : K.isoBot.hom ≫ A.ι = K.incl.app ⊥ := ((Iso.inv_comp_eq _).1 K.fac).symm
  have sq₀ : CommSq (K.isoBot.hom ≫ u) (K.incl.app ⊥) p w :=
    ⟨by rw [Category.assoc, sq.w, ← Category.assoc, hfac]⟩
  have key (j : ℕ) (_ : ¬IsMax j) (sq' : HasLiftingProperty.transfiniteComposition.SqStruct
      (Cocone.mk Z K.incl) p (K.isoBot.hom ≫ u) w j) : sq'.sq.HasLift := by
    let f := P.rankFunction
    have hcell (c : f.Cell j) :
        (⟨(Category.assoc _ _ _).trans ((congrArg (c.mapHorn ≫ ·) sq'.w₂).trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ w) c.mapHorn_ι).trans
            (Category.assoc _ _ _))))⟩ :
          CommSq (c.mapHorn ≫ sq'.f') c.horn.ι p (c.map ≫ w)).HasLift := by
      refine h c.s _ _ fun k y hy ↦ ?_
      have := congrArg (fun φ ↦ φ.app _ (K.isoBot.inv.app (op ⦋k⦌) ⟨_, hy⟩)) sq'.w₁
      exact this
    let L (c : f.Cell j) := (hcell c).exists_lift.some
    have hσ : f.t j ≫ sq'.f' = f.m j ≫ Sigma.desc fun c ↦ (L c).l :=
      Sigma.hom_ext _ _ fun c ↦ (c.ι_t_assoc sq'.f').trans (((L c).fac_left).symm.trans
        ((congrArg (c.horn.ι ≫ ·) (Sigma.ι_desc (fun c ↦ (L c).l) c).symm).trans
          (Subcomplex.Pairing.RankFunction.Cell.ι_m_assoc f c _).symm))
    refine ⟨⟨⟨(f.isPushout j).desc sq'.f' _ hσ, (f.isPushout j).inl_desc _ _ _, ?_⟩⟩⟩
    apply (f.isPushout j).hom_ext
    · exact ((f.isPushout j).inl_desc_assoc _ _ _ _).trans sq'.w₂
    · refine ((f.isPushout j).inr_desc_assoc _ _ _ _).trans (Sigma.hom_ext _ _ fun c ↦ ?_)
      exact (Sigma.ι_desc_assoc _ _ _).trans ((L c).fac_right.trans
        ((c.ι_b_assoc _).trans (c.mapToSucc_ι_assoc w)).symm)
  obtain ⟨l⟩ := (hasLift_of_forall_sqStruct K.isColimit key sq₀).exists_lift
  refine ⟨⟨⟨l.l, ?_, l.fac_right⟩⟩⟩
  calc A.ι ≫ l.l = (K.isoBot.inv ≫ K.incl.app ⊥) ≫ l.l := by rw [K.fac]
    _ = u := by rw [Category.assoc, l.fac_left, Iso.inv_hom_id_assoc]

end CellLifting

section UnionProd

private lemma hasLift_unionProd_horn_zero {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p]
    [X.Quasicategory] [Y.Quasicategory] {m n : ℕ}
    (hA : ∀ (z : (Δ[m + 1] ⊗ Δ[n] : SSet.{u}) _⦋1⦌), z.1 0 = 0 → z.1 1 = 1 → z.2 0 = 0 →
      z.2 1 = 0 → z ∈ (Subcomplex.unionProd Λ[m + 1, 0] ∂Δ[n]).obj _)
    {u : (Subcomplex.unionProd Λ[m + 1, 0] ∂Δ[n] : SSet.{u}) ⟶ X} {w : Δ[m + 1] ⊗ Δ[n] ⟶ Y}
    (sq : CommSq u (Subcomplex.unionProd Λ[m + 1, 0] ∂Δ[n]).ι p w)
    (hu : ∀ (z : (Subcomplex.unionProd Λ[m + 1, 0] ∂Δ[n] : SSet.{u}) _⦋1⦌),
      z.1.1 0 = 0 → z.1.1 1 = 1 → z.1.2 0 = 0 → z.1.2 1 = 0 →
        Nonempty (Edge.mk' (u.app _ z)).InvStruct) :
    sq.HasLift := by
  let h := prodStdSimplex.pairingCore.{u} (0 : Fin (m + 1)) n
  refine hasLift_of_pairing h.pairing sq fun x ↦ ?_
  obtain ⟨s, rfl⟩ := h.equivII.surjective x
  have hσ : ((h.pairing.p (h.equivII s)).val.cast
      (h.pairing.isUniquelyCodimOneFace (h.equivII s)).dim_eq).simplex =
        (s.x.cast s.hd).simplex := by
    have key : ∀ (y : (Subcomplex.unionProd Λ[m + 1, 0] ∂Δ[n]).N) (hy : y.dim = s.d + 1),
        y = s.x → (y.cast hy).simplex = (s.x.cast s.hd).simplex := by
      rintro _ _ rfl
      rfl
    exact key _ _ ((h.type₁_pairing s).symm.trans (prodStdSimplex.type₁_pairingCore _ s))
  rw [hσ, Subcomplex.PairingCore.pairing_isUniquelyCodimOneFace_index]
  intro a hab hcompat
  obtain ⟨y, d, hd, l, hl⟩ := s
  by_cases h0 : l = 0
  · subst h0
    have h₀ : (y.cast hd).simplex.2 (Fin.castSucc 0) = 0 := by
      obtain ⟨i, hi⟩ := prodStdSimplex.pairingCore.mem_range_right y hd 0
      exact nonpos_iff_eq_zero.1 (hi ▸ stdSimplex.monotone_apply _ (Fin.zero_le i))
    have h₁ := hl.simplex_snd_succ.trans h₀
    cases d with
    | zero =>
      exact ((y.cast hd).notMem (hA _ hl.simplex_fst_castSucc hl.simplex_fst_succ h₀ h₁)).elim
    | succ d =>
      have hy : (yonedaEquiv.symm (y.cast hd).simplex).app _
          (horn.edge (d + 2) 0 0 1 (Fin.zero_le _) (by simp)).1 ∈
            (Subcomplex.unionProd Λ[m + 1, 0] ∂Δ[n]).obj _ :=
        hA _ hl.simplex_fst_castSucc hl.simplex_fst_succ h₀ h₁
      refine hasLift_horn_zero_of_invStruct p (n := d) hab ⟨((hu ⟨_, hy⟩
        hl.simplex_fst_castSucc hl.simplex_fst_succ h₀ h₁).some).ofEq ?_⟩
      exact (hcompat 1 (horn.edge (d + 2) 0 0 1 (Fin.zero_le _) (by simp)) hy).symm
  · have : HasLiftingProperty (horn (d + 1) (Fin.castSucc l)).ι p :=
      mem_innerFibrations p _ (horn_ι_mem_innerHornInclusions
        (Fin.pos_iff_ne_zero.2 (by simpa using h0)) (Fin.castSucc_lt_last l))
    exact this.sq_hasLift hab

private lemma mem_boundary_of_eq {n : ℕ} (s : (Δ[n + 1] : SSet.{u}) _⦋1⦌) (h : s 0 = s 1) :
    s ∈ (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex).obj _ := by
  intro hs
  have key (i : Fin 2) : s i = s 0 := by
    fin_cases i
    · rfl
    · exact h.symm
  obtain ⟨a, ha⟩ := hs 0
  obtain ⟨c, hc⟩ := hs (Fin.last _)
  exact Fin.last_pos.ne ((ha.symm.trans (key a)).trans ((key c).symm.trans hc))

theorem hasLift_unionProd_horn_one_zero {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p]
    [X.Quasicategory] [Y.Quasicategory] {n : ℕ}
    {u : (Subcomplex.unionProd Λ[1, 0] ∂Δ[n + 1] : SSet.{u}) ⟶ X} {w : Δ[1] ⊗ Δ[n + 1] ⟶ Y}
    (sq : CommSq u (Subcomplex.unionProd Λ[1, 0] ∂Δ[n + 1]).ι p w)
    (hu : ∀ (z : (Subcomplex.unionProd Λ[1, 0] ∂Δ[n + 1] : SSet.{u}) _⦋1⦌),
      z.1.1 0 = 0 → z.1.1 1 = 1 → z.1.2 0 = 0 → z.1.2 1 = 0 →
        Nonempty (Edge.mk' (u.app _ z)).InvStruct) :
    sq.HasLift :=
  hasLift_unionProd_horn_zero p (m := 0) (fun _ _ _ h₀ h₁ ↦ (Subcomplex.mem_unionProd_iff _ _ _).2
    (Or.inl (mem_boundary_of_eq _ (h₀.trans h₁.symm)))) sq hu

end UnionProd

private lemma const_app_eq {K : SSet.{u}} {n : ℕ} (s : (∂Δ[n + 1] : SSet.{u}) _⦋1⦌)
    (h : s.1 0 = s.1 1) (y : K _⦋1⦌) :
    (stdSimplex.isTerminalObj₀.from K ≫
      yonedaEquiv.symm ((∂Δ[n + 1] : SSet.{u}).δ 1 s)).app _ y = s := by
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  fin_cases i
  · rfl
  · exact h

private lemma hasLiftingProperty_pullbackObjObjπ_succ_of_horn_zero {K : SSet.{u}}
    (v : K ⟶ coherentIso.{u})
    (hv : ∀ {E B : SSet.{u}} (q : E ⟶ B), (∀ m : ℕ, HasLiftingProperty Λ[m + 1, 0].ι q) →
      HasLiftingProperty v q) {X Y : SSet.{u}}
    (p : X ⟶ Y) [InnerFibration p] [X.Quasicategory] [Y.Quasicategory] (n : ℕ) :
    HasLiftingProperty v
      (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom
        (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι p).π := by
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom
    (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι p
  let adj := MonoidalClosed.internalHomAdjunction₂ (C := SSet.{u})
  refine ⟨fun {top bot} sq ↦ ?_⟩
  have hq (m : ℕ) : HasLiftingProperty Λ[m + 1, 0].ι (pullback.snd sq₁₃.π bot) := by
    refine ⟨fun {a c} sqm ↦ ?_⟩
    have w : (a ≫ pullback.fst _ _) ≫ sq₁₃.π = Λ[m + 1, 0].ι ≫ c ≫ bot := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, sqm.w, Category.assoc]
    let β : Arrow.mk Λ[m + 1, 0].ι ⟶ Arrow.mk sq₁₃.π := Arrow.homMk _ _ w
    let sq₁₂ := (Subcomplex.unionProd.pushoutObjObj Λ[m + 1, 0] ∂Δ[n + 1]).flipTensor
    let α := (adj.arrowHomEquiv sq₁₂ sq₁₃).symm β
    have hα : sq₁₂.inr ≫ α.left =
        ((∂Δ[n + 1] : SSet.{u}) ◁ c) ≫ adj.homEquiv.symm (bot ≫ sq₁₃.fst) :=
      (adj.inr_arrowHomEquiv_symm_apply_left sq₁₂ sq₁₃ β).trans
        ((congrArg _ (Category.assoc _ _ _)).trans (adj.homEquiv_symm_naturality_two _ _))
    have sqα : CommSq α.left (Subcomplex.unionProd Λ[m + 1, 0] ∂Δ[n + 1]).ι p
        ((β_ _ _).hom ≫ α.right) :=
      ⟨(Arrow.w α).trans (Category.assoc _ _ _)⟩
    have hlift : sqα.HasLift := by
      refine hasLift_unionProd_horn_zero p (fun z _ _ h₀ h₁ ↦ ?_) sqα (fun z _ _ h₀ h₁ ↦ ?_)
      · exact (Subcomplex.mem_unionProd_iff _ _ _).2
          (Or.inl (mem_boundary_of_eq _ (h₀.trans h₁.symm)))
      · have h := h₀.trans h₁.symm
        let s : (∂Δ[n + 1] : SSet.{u}) _⦋1⦌ := ⟨z.1.2, mem_boundary_of_eq _ h⟩
        let w : ((∂Δ[n + 1] : SSet.{u}) ⊗ Δ[m + 1] : SSet.{u}) _⦋1⦌ := (s, z.1.1)
        have hz : α.left.app _ z = (adj.homEquiv.symm (bot ≫ sq₁₃.fst)).app (op ⦋1⦌)
            (((s, c.app _ z.1.1)) : ((∂Δ[n + 1] : SSet.{u}) ⊗ coherentIso.{u} : SSet.{u}) _⦋1⦌) :=
          ConcreteCategory.congr_hom (congr_app hα _) w
        let f : coherentIso.{u} ⟶ (∂Δ[n + 1] : SSet.{u}) ⊗ coherentIso.{u} :=
          CartesianMonoidalCategory.lift (stdSimplex.isTerminalObj₀.from _ ≫
            yonedaEquiv.symm ((∂Δ[n + 1] : SSet.{u}).δ 1 s)) (𝟙 _)
        have hf : f.app _ (c.app _ z.1.1) = (s, c.app _ z.1.1) :=
          Prod.ext (const_app_eq s h _) rfl
        have key (x y : X _⦋1⦌) (hxy : x = y) (hy : Nonempty (Edge.mk' y).InvStruct) :
            Nonempty (Edge.mk' x).InvStruct := hxy ▸ hy
        exact key _ _ (hz.trans (congrArg _ hf.symm))
          (coherentIso.nonempty_invStruct_app (f ≫ adj.homEquiv.symm (bot ≫ sq₁₃.fst)) _)
    obtain ⟨l⟩ := hlift.exists_lift
    let L : Arrow.LiftStruct α :=
      ⟨(β_ _ _).inv ≫ l.l, (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc _ _)).trans l.fac_left),
        (Category.assoc _ _ _).trans ((congrArg _ l.fac_right).trans (Iso.inv_hom_id_assoc _ _))⟩
    let L' := adj.liftStructEquiv sq₁₂ sq₁₃ α L
    have e : adj.arrowHomEquiv sq₁₂ sq₁₃ α = β := Equiv.apply_symm_apply _ _
    have hl : Λ[m + 1, 0].ι ≫ L'.l = a ≫ pullback.fst _ _ :=
      L'.fac_left.trans (congrArg (fun φ ↦ φ.left) e)
    have hr : L'.l ≫ sq₁₃.π = c ≫ bot := L'.fac_right.trans (congrArg (fun φ ↦ φ.right) e)
    exact ⟨⟨⟨pullback.lift L'.l c hr, pullback.hom_ext
      (by rw [Category.assoc, pullback.lift_fst, hl])
      (by rw [Category.assoc, pullback.lift_snd, sqm.w]),
      pullback.lift_snd _ _ _⟩⟩⟩
  have sq' : CommSq (pullback.lift top _ sq.w) v (pullback.snd sq₁₃.π bot) (𝟙 _) :=
    ⟨by rw [pullback.lift_snd, Category.comp_id]⟩
  obtain ⟨l⟩ := ((hv _ hq).sq_hasLift sq').exists_lift
  exact ⟨⟨⟨l.l ≫ pullback.fst _ _, by rw [← Category.assoc, l.fac_left, pullback.lift_fst], by
    rw [Category.assoc, pullback.condition, ← Category.assoc, l.fac_right, Category.id_comp]⟩⟩⟩

theorem hasLiftingProperty_coherentIso_hom_pullbackObjObjπ_succ {X Y : SSet.{u}} (p : X ⟶ Y)
    [InnerFibration p] [X.Quasicategory] [Y.Quasicategory] (n : ℕ) :
    HasLiftingProperty (yonedaEquiv.symm coherentIso.hom.edge : Δ[1] ⟶ coherentIso.{u})
      (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom
        (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι p).π := by
  have := coherentIso.mono_hom_edge.{u}
  exact hasLiftingProperty_pullbackObjObjπ_succ_of_horn_zero _ (fun q hq ↦
    hasLiftingProperty_of_range_ι _ _ (coherentIso.hasLiftingProperty_ι_of_horn_zero false 1 _
      coherentIso.mem_range_hom_iff q hq)) p n

private def stdSimplexZeroTensorIso (K : SSet.{u}) : (Δ[0] : SSet.{u}) ⊗ K ≅ K where
  hom := CartesianMonoidalCategory.snd _ _
  inv := CartesianMonoidalCategory.lift (stdSimplex.isTerminalObj₀.from K) (𝟙 K)
  hom_inv_id := CartesianMonoidalCategory.hom_ext _ _ (stdSimplex.isTerminalObj₀.hom_ext _ _)
    (by simp)

private lemma hasLiftingProperty_vertex_pullbackObjObjπ_zero (b : Bool) {X Y : SSet.{u}}
    (p : X ⟶ Y) [Isofibration p] [X.Quasicategory] [Y.Quasicategory] :
    HasLiftingProperty (yonedaEquiv.symm (cond b coherentIso.x₁ coherentIso.x₀) :
      Δ[0] ⟶ coherentIso.{u})
      (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom
        (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex).ι p).π := by
  rw [← MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff
    (Functor.PushoutObjObj.ofIsInitialLeft (curriedTensor SSet.{u}) _ _ isInitialBoundaryZero)]
  refine (HasLiftingProperty.iff_of_arrow_iso_left (Arrow.isoMk (stdSimplexZeroTensorIso _)
    (stdSimplexZeroTensorIso _) ?_) p).2 (hasLiftingProperty_coherentIso_vertex b p)
  exact (CartesianMonoidalCategory.whiskerLeft_snd _ _).symm

theorem hasLiftingProperty_pullbackObjObjπ_comm {A B K L X Y : SSet.{u}} (v : A ⟶ B)
    (i : K ⟶ L) (p : X ⟶ Y) (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p)
    (sq₁₃' : MonoidalClosed.internalHom.PullbackObjObj v p) :
    HasLiftingProperty v sq₁₃.π ↔ HasLiftingProperty i sq₁₃'.π := by
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i v
  rw [← MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂,
    HasLiftingProperty.iff_of_arrow_iso_left
      (show Arrow.mk sq₁₂.ι ≅ Arrow.mk sq₁₂.flipTensor.ι from
        Arrow.isoMk (Iso.refl _) (β_ _ _)),
    MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃']

private lemma hasLiftingProperty_pullbackObjObjπ_of_boundary {A B X Y : SSet.{u}} (v : A ⟶ B)
    (p : X ⟶ Y) (h : ∀ n : ℕ, HasLiftingProperty v (Functor.PullbackObjObj.ofHasPullback
      MonoidalClosed.internalHom (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex).ι p).π)
    {K L : SSet.{u}} (i : K ⟶ L) [Mono i] (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p) :
    HasLiftingProperty v sq₁₃.π := by
  let sq₁₃' := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom v p
  rw [hasLiftingProperty_pullbackObjObjπ_comm v i p sq₁₃ sq₁₃']
  suffices (MorphismProperty.monomorphisms _).rlp sq₁₃'.π from this _ inferInstance
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  exact (hasLiftingProperty_pullbackObjObjπ_comm v _ p _ sq₁₃').1 (h n)

theorem hasLiftingProperty_coherentIso_vertex_pullbackObjObjπ (b : Bool) {X Y : SSet.{u}}
    (p : X ⟶ Y) [Isofibration p] [X.Quasicategory] [Y.Quasicategory] {K L : SSet.{u}}
    (i : K ⟶ L) [Mono i] (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p) :
    HasLiftingProperty (yonedaEquiv.symm (cond b coherentIso.x₁ coherentIso.x₀) :
      Δ[0] ⟶ coherentIso.{u}) sq₁₃.π := by
  refine hasLiftingProperty_pullbackObjObjπ_of_boundary _ p (fun n ↦ ?_) i sq₁₃
  cases n with
  | zero => exact hasLiftingProperty_vertex_pullbackObjObjπ_zero b p
  | succ n =>
    exact hasLiftingProperty_pullbackObjObjπ_succ_of_horn_zero _
      (fun q hq ↦ hasLiftingProperty_coherentIso_vertex_of_horn_zero b q hq) p n

lemma quasicategory_pullbackObjObj_pt {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p]
    [Y.Quasicategory] {K L : SSet.{u}} (i : K ⟶ L)
    (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p) : sq₁₃.pt.Quasicategory := by
  have : InnerFibration sq₁₃.snd :=
    ⟨MorphismProperty.of_isPullback (P := innerFibrations) sq₁₃.isPullback
      (mem_innerFibrations ((ihom K).map p))⟩
  have hL : ((ihom L).obj Y).Quasicategory := inferInstance
  exact @quasicategory_of_innerFibration _ _ sq₁₃.snd _ hL

theorem isofibration_pullbackObjObjπ {X Y : SSet.{u}} (p : X ⟶ Y) [Isofibration p]
    [X.Quasicategory] [Y.Quasicategory] {K L : SSet.{u}} (i : K ⟶ L) [Mono i]
    (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p) : Isofibration sq₁₃.π := by
  have := quasicategory_pullbackObjObj_pt p i sq₁₃
  have := innerFibration_pullbackObjObjπ sq₁₃
  exact Isofibration.of_hasLiftingProperty_vertex _
    (hasLiftingProperty_coherentIso_vertex_pullbackObjObjπ false p i sq₁₃)

end SSet
