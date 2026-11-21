import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Atoms.ForMathlib.CategoryTheory.Subfunctor.Colimits

universe u

open CategoryTheory Limits MonoidalCategory Opposite Simplicial

namespace SSet

def diag : SimplicialObject SSet.{u} ⥤ SSet.{u} where
  obj X :=
    { obj n := (X.obj n).obj n
      map f := (X.map f).app _ ≫ (X.obj _).map f
      map_id n := by simp
      map_comp f g := by
        simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc,
          NatTrans.naturality_assoc] }
  map f :=
    { app n := (f.app n).app n
      naturality m n g := by
        simp only [Category.assoc]
        rw [← NatTrans.comp_app_assoc, ← f.naturality, NatTrans.comp_app_assoc,
          (f.app n).naturality] }

theorem diag_obj_obj (X : SimplicialObject SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (diag.obj X).obj n = (X.obj n).obj n := rfl

theorem diag_obj_map (X : SimplicialObject SSet.{u}) {m n : SimplexCategoryᵒᵖ} (g : m ⟶ n) :
    (diag.obj X).map g = (X.map g).app m ≫ (X.obj n).map g := rfl

@[simp]
theorem diag_map_app {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    (diag.map f).app n = (f.app n).app n := rfl

def transpose : SimplicialObject SSet.{u} ⥤ SimplicialObject SSet.{u} :=
  flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)

def diagTransposeIso : transpose.{u} ⋙ diag ≅ diag :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun n ↦ Iso.refl _) fun g ↦ by
    ext x
    exact NatTrans.naturality_apply (X.map g) g x) fun f ↦ by
      ext n x
      rfl

variable (X : SimplicialObject SSet.{u})

def fromConst : (Functor.const SimplexCategoryᵒᵖ).obj (X _⦋0⦌) ⟶ X where
  app n := X.map (SimplexCategory.isTerminalZero.from n.unop).op
  naturality n n' g := by
    refine (Category.id_comp _).trans ?_
    rw [← X.map_comp]
    congr 1

theorem fromConst_app (n : SimplexCategoryᵒᵖ) :
    (fromConst X).app n = X.map (SimplexCategory.isTerminalZero.from n.unop).op := rfl

omit X in
def diagConstIso (K : SSet.{u}) : diag.obj ((Functor.const SimplexCategoryᵒᵖ).obj K) ≅ K :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ by
    ext x
    rfl

def toDiag : X _⦋0⦌ ⟶ diag.obj X :=
  (diagConstIso (X _⦋0⦌)).inv ≫ diag.map (fromConst X)

theorem toDiag_app_apply (n : SimplexCategoryᵒᵖ) (x : (X _⦋0⦌).obj n) :
    (toDiag X).app n x = (X.map (SimplexCategory.isTerminalZero.from n.unop).op).app n x := rfl

omit X in
theorem toDiag_naturality {X X' : SimplicialObject SSet.{u}} (f : X ⟶ X') :
    toDiag X ≫ diag.map f = f.app (op ⦋0⦌) ≫ toDiag X' := by
  ext n x
  exact congrArg (fun g : X _⦋0⦌ ⟶ X'.obj n ↦ g.app n x)
    (f.naturality (SimplexCategory.isTerminalZero.from n.unop).op)

def cellMap (n : ℕ) : X _⦋n⦌ ⊗ Δ[n] ⟶ diag.obj X where
  app k := TypeCat.ofHom fun p ↦ (X.map (stdSimplex.objEquiv p.2).op).app k p.1
  naturality k k' g := by
    ext ⟨y, s⟩
    change (X.map (g.unop ≫ stdSimplex.objEquiv s).op).app k' ((X _⦋n⦌).map g y) =
      (X.obj k').map g ((X.map g).app k ((X.map (stdSimplex.objEquiv s).op).app k y))
    rw [op_comp, Functor.map_comp, NatTrans.comp_app, ConcreteCategory.comp_apply,
      NatTrans.naturality_apply, NatTrans.naturality_apply]
    rfl

@[reassoc]
theorem cellMap_naturality {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    cellMap X n ≫ diag.map f = (f.app _ ▷ Δ[n]) ≫ cellMap Y n := by
  ext k ⟨y, s⟩
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality _) k) y

def diagSkeleton (n : ℕ) : (diag.obj X).Subcomplex :=
  ⨆ (j : ℕ) (_ : j < n), Subcomplex.range (cellMap X j)

theorem mem_diagSkeleton_iff (n : ℕ) {k : SimplexCategoryᵒᵖ} (x : (diag.obj X).obj k) :
    x ∈ (diagSkeleton X n).obj k ↔ ∃ j < n, ∃ p, (cellMap X j).app k p = x := by
  simp [diagSkeleton]

theorem diagSkeleton_zero : diagSkeleton X 0 = ⊥ := by
  simp [diagSkeleton]

theorem diagSkeleton_succ (n : ℕ) :
    diagSkeleton X (n + 1) = diagSkeleton X n ⊔ Subcomplex.range (cellMap X n) := by
  ext k x
  simp only [Subfunctor.max_obj, Set.mem_union, mem_diagSkeleton_iff, Subfunctor.range_obj,
    Set.mem_range, Nat.lt_succ_iff_lt_or_eq]
  constructor
  · rintro ⟨j, hj | rfl, h⟩
    · exact Or.inl ⟨j, hj, h⟩
    · exact Or.inr h
  · rintro (⟨j, hj, h⟩ | h)
    · exact ⟨j, Or.inl hj, h⟩
    · exact ⟨n, Or.inr rfl, h⟩

theorem diagSkeleton_mono {m n : ℕ} (h : m ≤ n) : diagSkeleton X m ≤ diagSkeleton X n := by
  intro k x hx
  obtain ⟨j, hj, hx⟩ := (mem_diagSkeleton_iff X m x).1 hx
  exact (mem_diagSkeleton_iff X n x).2 ⟨j, hj.trans_le h, hx⟩

theorem iSup_diagSkeleton : ⨆ n, diagSkeleton X n = ⊤ := by
  refine eq_top_iff.2 fun k x _ ↦ ?_
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
  refine ⟨k.unop.len + 1, (mem_diagSkeleton_iff X _ x).2
    ⟨k.unop.len, Nat.lt_succ_self _, ⟨x, stdSimplex.objEquiv.{u}.symm (𝟙 k.unop)⟩, ?_⟩⟩
  change (X.map (stdSimplex.objEquiv.{u} (stdSimplex.objEquiv.{u}.symm (𝟙 k.unop))).op).app k x = x
  rw [Equiv.apply_symm_apply, op_id, X.map_id]
  rfl

theorem range_cellMap_le (n : ℕ) : Subcomplex.range (cellMap X n) ≤ diagSkeleton X (n + 1) := by
  rw [diagSkeleton_succ]
  exact le_sup_right

theorem diagSkeleton_le_preimage {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    diagSkeleton X n ≤ (diagSkeleton Y n).preimage (diag.map f) := by
  intro k x hx
  obtain ⟨j, hj, p, rfl⟩ := (mem_diagSkeleton_iff X n x).1 hx
  refine (mem_diagSkeleton_iff Y n _).2 ⟨j, hj, (f.app _ ▷ Δ[j]).app k p, ?_⟩
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app (cellMap_naturality f j) k) p).symm

def latching (n : ℕ) : (X _⦋n⦌).Subcomplex where
  obj k := ((transpose.obj X).obj k).degenerate n
  map g _ hx := degenerate_app_apply hx ((transpose.obj X).map g)

theorem mem_latching_iff (n : ℕ) {k : SimplexCategoryᵒᵖ} (y : (X _⦋n⦌).obj k) :
    y ∈ (latching X n).obj k ↔ y ∈ ((transpose.obj X).obj k).degenerate n := Iff.rfl

theorem latching_zero : latching X 0 = ⊥ := by
  ext k x
  simp only [mem_latching_iff, degenerate_zero, Subfunctor.bot_obj, Set.bot_eq_empty]
  exact Iff.rfl

theorem latching_le_preimage {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    latching X n ≤ (latching Y n).preimage (f.app _) :=
  fun k y hy ↦ by
    have := degenerate_app_apply (x := y) (n := n) hy ((transpose.map f).app k)
    exact this

omit X in
private theorem map_app_map_app (X : SimplicialObject SSet.{u}) {a b c : SimplexCategoryᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (k : SimplexCategoryᵒᵖ) (y : (X.obj a).obj k) :
    (X.map g).app k ((X.map f).app k y) = (X.map (f ≫ g)).app k y := by
  rw [X.map_comp]
  rfl

theorem cellMap_app_map {m n : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (k : SimplexCategoryᵒᵖ) (y : (X _⦋m⦌).obj k)
    (σ : k.unop ⟶ ⦋n⦌) :
    (cellMap X n).app k ⟨(X.map f.op).app k y, stdSimplex.objEquiv.symm σ⟩ =
      (cellMap X m).app k ⟨y, stdSimplex.objEquiv.symm (σ ≫ f)⟩ :=
  map_app_map_app X f.op σ.op k y

theorem preimage_cellMap (n : ℕ) :
    (diagSkeleton X n).preimage (cellMap X n) = (latching X n).unionProd ∂Δ[n] := by
  ext k ⟨y, s⟩
  refine (mem_diagSkeleton_iff X n ((cellMap X n).app k ⟨y, s⟩)).trans
    (Iff.trans ?_ (Subcomplex.mem_unionProd_iff _ _ ⟨y, s⟩).symm)
  constructor
  · rintro ⟨j, hj, ⟨z, t⟩, h⟩
    by_contra hc
    obtain ⟨hs, hy⟩ := not_or.1 hc
    have : Epi (stdSimplex.objEquiv s) := SimplexCategory.epi_iff_surjective.2 (not_not.1 hs)
    obtain ⟨⟨sec⟩⟩ := isSplitEpi_of_epi (stdSimplex.objEquiv s)
    refine hy ⟨j, hj, sec.section_ ≫ stdSimplex.objEquiv t, z, ?_⟩
    have h' := congrArg ((X.map sec.section_.op).app k) h
    refine ((map_app_map_app X _ _ k z).symm.trans h').trans ?_
    refine (map_app_map_app X _ _ k y).trans ?_
    rw [← op_comp, sec.id, op_id, X.map_id]
    rfl
  · rintro (hs | ⟨m, hm, f, z, rfl⟩)
    · cases n with
      | zero => simp [boundary_zero] at hs
      | succ n =>
        obtain ⟨i, θ, hθ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective _ hs
        refine ⟨n, n.lt_succ_self, ⟨(X.δ i).app k y, stdSimplex.objEquiv.symm θ⟩, ?_⟩
        refine (cellMap_app_map X (SimplexCategory.δ i) k y θ).trans ?_
        rw [← hθ]
        rfl
    · refine ⟨m, hm, ⟨z, stdSimplex.objEquiv.symm (stdSimplex.objEquiv s ≫ f)⟩, ?_⟩
      have := cellMap_app_map X f k z (stdSimplex.objEquiv s)
      rw [Equiv.symm_apply_apply] at this
      exact this.symm

theorem cellMap_injective_off (n : ℕ) (k : SimplexCategoryᵒᵖ)
    (p q : (X _⦋n⦌ ⊗ Δ[n]).obj k) (hp : p ∉ ((latching X n).unionProd ∂Δ[n]).obj k)
    (hq : q ∉ ((latching X n).unionProd ∂Δ[n]).obj k)
    (h : (cellMap X n).app k p = (cellMap X n).app k q) : p = q := by
  obtain ⟨y, s⟩ := p
  obtain ⟨y', s'⟩ := q
  obtain ⟨hs, hy⟩ := not_or.1 fun h ↦ hp ((Subcomplex.mem_unionProd_iff _ _ ⟨y, s⟩).2 h)
  obtain ⟨hs', hy'⟩ := not_or.1 fun h ↦ hq ((Subcomplex.mem_unionProd_iff _ _ ⟨y', s'⟩).2 h)
  have : Epi (stdSimplex.objEquiv s) := SimplexCategory.epi_iff_surjective.2 (not_not.1 hs)
  have : Epi (stdSimplex.objEquiv s') := SimplexCategory.epi_iff_surjective.2 (not_not.1 hs')
  induction k using Opposite.rec with | op k => ?_
  obtain ⟨d⟩ := k
  let S := (transpose.obj X).obj (op ⦋d⦌)
  have e := S.unique_nonDegenerate_simplex _ (stdSimplex.objEquiv s) ⟨y, hy⟩ rfl
    (stdSimplex.objEquiv s') ⟨y', hy'⟩ h
  have e' := S.unique_nonDegenerate_map _ (stdSimplex.objEquiv s) ⟨y, hy⟩ rfl
    (stdSimplex.objEquiv s') ⟨y', hy'⟩ h
  obtain rfl : y = y' := congrArg Subtype.val e
  rw [stdSimplex.objEquiv.injective e']

theorem isPushout_diagSkeleton (n : ℕ) :
    IsPushout ((latching X n).unionProd ∂Δ[n]).ι
      (Subcomplex.lift (((latching X n).unionProd ∂Δ[n]).ι ≫ cellMap X n)
        (by rw [← preimage_cellMap]; exact fun k _ ⟨⟨_, hx⟩, h⟩ ↦ h ▸ hx))
      (Subcomplex.lift (cellMap X n) (range_cellMap_le X n))
      (Subcomplex.homOfLE (diagSkeleton_mono X n.le_succ)) :=
  Subfunctor.isPushout_of_preimage _ _ (preimage_cellMap X n) (diagSkeleton_succ X n).symm
    (cellMap_injective_off X n)

def latchingFiltration (m j : ℕ) : (X _⦋m + 1⦌).Subcomplex :=
  ⨆ (i : Fin (m + 1)) (_ : i.1 < j), Subcomplex.range (X.σ i)

theorem mem_latchingFiltration_iff (m j : ℕ) {k : SimplexCategoryᵒᵖ} (x : (X _⦋m + 1⦌).obj k) :
    x ∈ (latchingFiltration X m j).obj k ↔
      ∃ i : Fin (m + 1), i.1 < j ∧ ∃ z, (X.σ i).app k z = x := by
  simp [latchingFiltration]

theorem latchingFiltration_zero (m : ℕ) : latchingFiltration X m 0 = ⊥ := by
  simp [latchingFiltration]

theorem latchingFiltration_succ (m j : ℕ) (hj : j < m + 1) :
    latchingFiltration X m (j + 1) =
      latchingFiltration X m j ⊔ Subcomplex.range (X.σ ⟨j, hj⟩) := by
  ext k x
  simp only [Subfunctor.max_obj, Set.mem_union, mem_latchingFiltration_iff, Subfunctor.range_obj,
    Set.mem_range]
  constructor
  · rintro ⟨i, hi, h⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · exact Or.inl ⟨i, hi, h⟩
    · obtain rfl : i = ⟨j, hj⟩ := Fin.ext hi
      exact Or.inr h
  · rintro (⟨i, hi, h⟩ | h)
    · exact ⟨i, hi.trans (Nat.lt_succ_self j), h⟩
    · exact ⟨⟨j, hj⟩, Nat.lt_succ_self j, h⟩

theorem latchingFiltration_self (m : ℕ) : latchingFiltration X m (m + 1) = latching X (m + 1) := by
  ext k x
  rw [mem_latchingFiltration_iff, mem_latching_iff, degenerate_eq_iUnion_range_σ]
  refine ⟨fun ⟨i, _, h⟩ ↦ Set.mem_iUnion.2 ⟨i, h⟩, fun h ↦ ?_⟩
  obtain ⟨i, h⟩ := Set.mem_iUnion.1 h
  exact ⟨i, i.2, h⟩

theorem latchingFiltration_inf_range (m : ℕ) (J : Fin (m + 2)) :
    latchingFiltration X (m + 1) J ⊓ Subcomplex.range (X.σ J) =
      Subcomplex.range ((latchingFiltration X m J).ι ≫ X.σ J) := by
  ext k x
  simp only [Subfunctor.min_obj, Set.mem_inter_iff, mem_latchingFiltration_iff,
    Subfunctor.range_obj, Set.mem_range]
  constructor
  · rintro ⟨⟨i, hi, z, rfl⟩, y, hy⟩
    have hiJ : i.1 < m + 1 := lt_of_lt_of_le hi (Nat.lt_succ_iff.1 J.2)
    refine ⟨⟨y, (mem_latchingFiltration_iff X m J y).2 ⟨i.castLT hiJ, hi,
      (X.δ J).app k z, ?_⟩⟩, hy⟩
    have h₁ : (X.δ J.succ).app k ((X.σ i).app k z) =
        (X.σ (i.castLT hiJ)).app k ((X.δ (J.succ.pred (Fin.succ_ne_zero J))).app k z) :=
      ConcreteCategory.congr_hom (NatTrans.congr_app
        (X.δ_comp_σ_of_gt' (i := J.succ) (j := i) (Fin.succ_lt_succ_iff.2 hi)) k) z
    have h₂ : (X.δ J.succ).app k ((X.σ J).app k y) = y :=
      ConcreteCategory.congr_hom (NatTrans.congr_app (X.δ_comp_σ_succ (i := J)) k) y
    rw [hy, h₁, Fin.pred_succ] at h₂
    exact h₂
  · rintro ⟨⟨w, hw⟩, rfl⟩
    obtain ⟨i, hi, v, rfl⟩ := (mem_latchingFiltration_iff X m J w).1 hw
    have hJ : J ≠ 0 := fun h ↦ by simp [h] at hi
    refine ⟨⟨i.castSucc, hi, (X.σ (J.pred hJ)).app k v, ?_⟩, _, rfl⟩
    have hle : i ≤ J.pred hJ := (Fin.le_pred_iff hJ).2 (Fin.le_iff_val_le_val.2 (by
      rw [Fin.val_succ]
      exact hi))
    have h : (X.σ i.castSucc).app k ((X.σ (J.pred hJ)).app k v) =
        (X.σ (J.pred hJ).succ).app k ((X.σ i).app k v) :=
      ConcreteCategory.congr_hom (NatTrans.congr_app (X.σ_comp_σ hle) k) v
    rw [Fin.succ_pred] at h
    exact h

theorem latchingFiltration_le_preimage {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) (m j : ℕ) :
    latchingFiltration X m j ≤ (latchingFiltration Y m j).preimage (f.app _) := by
  intro k x hx
  obtain ⟨i, hi, z, rfl⟩ := (mem_latchingFiltration_iff X m j x).1 hx
  refine (mem_latchingFiltration_iff Y m j _).2 ⟨i, hi, (f.app _).app k z, ?_⟩
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality _) k) z).symm

end SSet
