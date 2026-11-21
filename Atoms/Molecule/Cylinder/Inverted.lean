import Atoms.Molecule.Cylinder.PartialMolecule

universe u

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

namespace PartialCylinderCarrier

variable {U : OGP.{u}} {K : LowerSet U}

def invertedOrientFn (ε : Bool) (n : ℕ) :
    ∀ a b : partialCylinder U K, b ⋖ a → Bool
  | Sum.inr (⟨none⟩, x), Sum.inr (⟨some β⟩, _), _ =>
      if grade ℕ x.1 = n then !ε else β
  | Sum.inr (⟨none⟩, _), Sum.inr (⟨none⟩, _), h => !U.orient (proj_covBy_of_covBy_inr_none h)
  | Sum.inr (⟨none⟩, _), Sum.inl _, h => (not_covBy_inl_inr_none h).elim
  | Sum.inr (⟨some β⟩, x), _, h =>
      if β = ε ∧ grade ℕ x.1 = n then !U.orient (proj_covBy_of_covBy_inr_some h)
      else U.orient (proj_covBy_of_covBy_inr_some h)
  | Sum.inl _, _, h => U.orient (proj_covBy_of_covBy_inl h)

end PartialCylinderCarrier

abbrev invertedCylinder (U : OGP.{u}) (K : LowerSet U) (ε : Bool) (n : ℕ) : OGP.{u} :=
  { partialCylinder U K with
    orient := fun {a b} h => PartialCylinderCarrier.invertedOrientFn ε n a b h }

namespace InvertedCylinder

open PartialCylinder

variable {U : OGP.{u}} {K : LowerSet U} {ε : Bool} {n : ℕ} {x y : U}

def changed (ε : Bool) (n : ℕ) : partialCylinder U K → Bool
  | Sum.inl _ => false
  | Sum.inr (⟨none⟩, x) => decide (n ≤ grade ℕ x.1)
  | Sum.inr (⟨some β⟩, x) => decide (β = ε ∧ n ≤ grade ℕ x.1)

theorem orient_of_covBy {a b : partialCylinder U K} (h : b ⋖ a) :
    (invertedCylinder U K ε n).orient h = PartialCylinderCarrier.invertedOrientFn ε n a b h :=
  rfl

theorem orient_eq_of_changed_eq_false {a b : partialCylinder U K}
    (ha : changed ε n a = false) (h : b ⋖ a) :
    (invertedCylinder U K ε n).orient h = (partialCylinder U K).orient h := by
  rcases a with ⟨x, hx⟩ | ⟨⟨_ | β⟩, ⟨x, hx⟩⟩
  · rfl
  · have hd : grade ℕ x ≠ n := fun he => by simp [changed, he] at ha
    rcases b with ⟨y, hy⟩ | ⟨⟨_ | γ⟩, ⟨y, hy⟩⟩
    · exact (PartialCylinderCarrier.not_covBy_inl_inr_none h).elim
    · rfl
    · change (if grade ℕ x = n then !ε else γ) = γ
      rw [if_neg hd]
  · have hβ : ¬ (β = ε ∧ grade ℕ x = n) := fun ⟨h1, h2⟩ => by simp [changed, h1, h2] at ha
    change (if β = ε ∧ grade ℕ x = n then _ else _) = _
    rw [if_neg hβ]
    rfl

theorem orient_mkI_none_mkI_some_top (hx : x ∉ K) (hd : grade ℕ x = n) (β : Bool)
    (h : mkI K (some β) x hx ⋖ mkI K none x hx) :
    (invertedCylinder U K ε n).orient h = !ε := by
  change (if grade ℕ x = n then !ε else β) = !ε
  rw [if_pos hd]

theorem orient_mkI_some_top (hx : x ∉ K) (hd : grade ℕ x = n)
    {b : partialCylinder U K} (h : b ⋖ mkI K (some ε) x hx)
    (hp : partialCylinderProj U K b ⋖ x) :
    (invertedCylinder U K ε n).orient h = !U.orient hp := by
  change (if ε = ε ∧ grade ℕ x = n then !U.orient hp else U.orient hp) = _
  rw [if_pos ⟨rfl, hd⟩]

variable (K ε n) in
def std : LowerSet (partialCylinder U K) where
  carrier := {a | changed ε n a = false}
  lower' := by
    rintro (a | ⟨⟨_ | γ⟩, a⟩) (b | ⟨⟨_ | β⟩, b⟩) hba ha
    · exact ha
    · exact hba.elim
    · exact hba.elim
    · rfl
    · change changed ε n _ = false at ha ⊢
      have ha' : ¬ n ≤ grade ℕ a.1 := by simpa [changed] using ha
      have hba' : b.1 ≤ a.1 := hba.2
      have hb' : ¬ n ≤ grade ℕ b.1 := fun h => ha' (h.trans (grade_mono hba'))
      simpa [changed] using hb'
    · change changed ε n _ = false at ha ⊢
      have ha' : ¬ n ≤ grade ℕ a.1 := by simpa [changed] using ha
      have hba' : b.1 ≤ a.1 := hba.2
      have hb' : ¬ (β = ε ∧ n ≤ grade ℕ b.1) := fun h => ha' (h.2.trans (grade_mono hba'))
      simpa [changed] using hb'
    · rfl
    · rcases hba.1 with h | h <;> cases h
    · change changed ε n _ = false at ha ⊢
      have ha' : ¬ (γ = ε ∧ n ≤ grade ℕ a.1) := by simpa [changed] using ha
      have hβγ : β = γ := by
        rcases hba.1 with h | h
        · exact Option.some_inj.1 h
        · cases h
      subst hβγ
      have hba' : b.1 ≤ a.1 := hba.2
      have hb' : ¬ (β = ε ∧ n ≤ grade ℕ b.1) := fun h => ha' ⟨h.1, h.2.trans (grade_mono hba')⟩
      simpa [changed] using hb'

@[simp] theorem mem_std {a : partialCylinder U K} :
    a ∈ std K ε n ↔ changed ε n a = false :=
  Iff.rfl

theorem mem_std_of_dim_lt {a : partialCylinder U K}
    (h : grade ℕ (partialCylinderProj U K a) < n) : a ∈ std K ε n := by
  rw [mem_std]
  rcases a with ⟨z, hz⟩ | ⟨⟨_ | β⟩, ⟨z, hz⟩⟩
  · rfl
  · have : ¬ n ≤ grade ℕ z := not_le.2 h
    simp [changed, this]
  · have : ¬ n ≤ grade ℕ z := not_le.2 h
    simp [changed, this]

theorem mkK_mem_std (hx : x ∈ K) : mkK K x hx ∈ std K ε n := rfl

theorem mkI_some_notMem_std (hx : x ∉ K) : mkI K (some (!ε)) x hx ∈ std K ε n := by
  rw [mem_std]
  cases ε <;> simp [changed]

variable (K ε n) in
def ofStd : (partialCylinder U K).restrict (std K ε n) ⟶ invertedCylinder U K ε n :=
  ConcreteCategory.ofHom ⟨Subtype.val, by
    have hc (x y : (partialCylinder U K).restrict (std K ε n)) :
        (y : invertedCylinder U K ε n) ⋖ x ↔ y ⋖ x :=
      OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype (· ∈ std K ε n))
        (by simpa [-mem_std] using (std K ε n).lower.ordConnected)
    refine ⟨fun x α => ⟨fun y hy => ⟨(hc x y).2 hy.1, ?_⟩, Subtype.val_injective.injOn,
      fun z hz => ⟨⟨z, (std K ε n).lower hz.1.le x.2⟩, ⟨(hc x ⟨z, _⟩).1 hz.1, ?_⟩, rfl⟩⟩⟩
    · exact (orient_eq_of_changed_eq_false x.2 ((hc x y).2 hy.1)).trans hy.2
    · exact (orient_eq_of_changed_eq_false x.2 hz.1).symm.trans hz.2⟩

@[simp] theorem ofStd_apply (a : (partialCylinder U K).restrict (std K ε n)) :
    ofStd K ε n a = a.1 :=
  rfl

instance : IsInclusion (ofStd K ε n) := ⟨Subtype.val_injective⟩

theorem map_ofStd_eq_map_incl (S : LowerSet ((partialCylinder U K).restrict (std K ε n))) :
    map (ofStd K ε n) S = map (incl (std K ε n)) S :=
  rfl

@[simp] theorem map_ofStd_top : map (ofStd K ε n) ⊤ = std K ε n :=
  map_incl_top (std K ε n)

theorem boundary_eq_of_subset_std {Y : LowerSet (partialCylinder U K)}
    (hY : Y ≤ std K ε n) (k : ℕ) (α : Bool) :
    (invertedCylinder U K ε n).boundary Y k α = (partialCylinder U K).boundary Y k α := by
  have h1 : map (incl (std K ε n)) (comap (incl (std K ε n)) Y) = Y :=
    map_comap_of_le (incl (std K ε n)) (by rwa [map_incl_top])
  have h2 : map (ofStd K ε n) (comap (incl (std K ε n)) Y) = Y := h1
  conv_lhs => rw [← h2, ← map_boundary]
  conv_rhs => rw [← h1, ← map_boundary]
  rfl

theorem isMoleculeIn_iff_of_subset_std {Y : LowerSet (partialCylinder U K)}
    (hY : Y ≤ std K ε n) :
    IsMoleculeIn (invertedCylinder U K ε n) Y ↔ IsMoleculeIn (partialCylinder U K) Y := by
  have h1 : map (incl (std K ε n)) (comap (incl (std K ε n)) Y) = Y :=
    map_comap_of_le (incl (std K ε n)) (by rwa [map_incl_top])
  have h2 : map (ofStd K ε n) (comap (incl (std K ε n)) Y) = Y := h1
  conv_lhs => rw [← h2]
  conv_rhs => rw [← h1]
  exact (isMoleculeIn_map_iff (ofStd K ε n) _).trans
    (isMoleculeIn_map_iff (incl (std K ε n)) _).symm

theorem round_iff_of_subset_std {Y : LowerSet (partialCylinder U K)}
    (hY : Y ≤ std K ε n) :
    (invertedCylinder U K ε n).IsRound Y ↔ (partialCylinder U K).IsRound Y := by
  have h1 : map (incl (std K ε n)) (comap (incl (std K ε n)) Y) = Y :=
    map_comap_of_le (incl (std K ε n)) (by rwa [map_incl_top])
  have h2 : map (ofStd K ε n) (comap (incl (std K ε n)) Y) = Y := h1
  conv_lhs => rw [← h2]
  conv_rhs => rw [← h1]
  exact (isRound_map_iff (ofStd K ε n) _).trans (isRound_map_iff (incl (std K ε n)) _).symm

theorem isSubmoleculeOf_of_subset_std {X Y : LowerSet (partialCylinder U K)}
    (hY : Y ≤ std K ε n) (h : (partialCylinder U K).IsSubmoleculeOf X Y) :
    (invertedCylinder U K ε n).IsSubmoleculeOf X Y := by
  have hX : X ≤ std K ε n := h.le.trans hY
  have hY1 : map (incl (std K ε n)) (comap (incl (std K ε n)) Y) = Y :=
    map_comap_of_le (incl (std K ε n)) (by rwa [map_incl_top])
  have hX1 : map (incl (std K ε n)) (comap (incl (std K ε n)) X) = X :=
    map_comap_of_le (incl (std K ε n)) (by rwa [map_incl_top])
  have h' : ((partialCylinder U K).restrict (std K ε n)).IsSubmoleculeOf
      (comap (incl (std K ε n)) X) (comap (incl (std K ε n)) Y) := by
    refine (isSubmoleculeOf_map_iff (incl (std K ε n))).1 ?_
    rwa [hX1, hY1]
  have h'' := (isSubmoleculeOf_map_iff (ofStd K ε n)).2 h'
  rwa [map_ofStd_eq_map_incl, map_ofStd_eq_map_incl, hX1, hY1] at h''

theorem mem_facesIn_iff_of_orient_eq {S : Set (partialCylinder U K)}
    {z : partialCylinder U K} {k : ℕ} {α : Bool}
    (h : ∀ c ∈ S, ∀ hcov : z ⋖ c,
      (invertedCylinder U K ε n).orient hcov = (partialCylinder U K).orient hcov) :
    z ∈ (invertedCylinder U K ε n).facesIn S k α ↔ z ∈ (partialCylinder U K).facesIn S k α := by
  simp only [facesIn, mem_ofPred_eq, disjoint_left, mem_cofaces]
  refine and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun hd c ⟨hcov, hor⟩ hcS => hd ⟨hcov, (h c hcS hcov).trans hor⟩ hcS,
      fun hd c ⟨hcov, hor⟩ hcS => hd ⟨hcov, (h c hcS hcov).symm.trans hor⟩ hcS⟩

theorem orient_eq_of_covBy_mkI_none (ha : x ∉ K) {c : partialCylinder U K}
    (hc : mkI K none x ha ⋖ c) :
    (invertedCylinder U K ε n).orient hc = (partialCylinder U K).orient hc := by
  rcases c with ⟨w, hw⟩ | ⟨⟨_ | γ⟩, ⟨w, hw⟩⟩
  · exact (PartialCylinderCarrier.not_inr_le_inl hc.1.le).elim
  · rfl
  · exact (not_covBy_mkI_none_mkI_some γ ha hw hc).elim

theorem mkI_none_mem_facesIn_over_iff {V : LowerSet U} {α : Bool} (hx : x ∉ K) :
    mkI K none x hx ∈ (invertedCylinder U K ε n).facesIn (over K V) (grade ℕ x + 1) α ↔
      x ∈ U.facesIn V (grade ℕ x) (!α) :=
  (mem_facesIn_iff_of_orient_eq fun _ _ hc => orient_eq_of_covBy_mkI_none hx hc).trans
    (mkI_none_mem_facesIn_over hx)

theorem endpoint_notMem_std [DecidablePred (· ∈ K)] (x : U) :
    partialCylinderEndpoint U K (!ε) x ∈ std K ε n := by
  by_cases hx : x ∈ K
  · rw [endpoint_of_mem _ hx]; exact mkK_mem_std hx
  · rw [endpoint_of_notMem _ hx]; exact mkI_some_notMem_std hx

def embOfStd {A : OGP.{u}} (f : A ⟶ partialCylinder U K) (hf : ∀ x, f x ∈ std K ε n) :
    A ⟶ invertedCylinder U K ε n :=
  codRestrict f (std K ε n) hf ≫ ofStd K ε n

@[simp] theorem embOfStd_apply {A : OGP.{u}} (f : A ⟶ partialCylinder U K)
    (hf : ∀ x, f x ∈ std K ε n) (x : A) :
    embOfStd f hf x = f x :=
  rfl

instance {A : OGP.{u}} (f : A ⟶ partialCylinder U K) [IsInclusion f]
    (hf : ∀ x, f x ∈ std K ε n) : IsInclusion (embOfStd f hf) :=
  inferInstanceAs (IsInclusion (codRestrict f (std K ε n) hf ≫ ofStd K ε n))

@[simp] theorem map_embOfStd {A : OGP.{u}} (f : A ⟶ partialCylinder U K)
    (hf : ∀ x, f x ∈ std K ε n) (S : LowerSet A) :
    map (embOfStd f hf) S = map f S :=
  rfl

variable (U K ε n) in
def endpointNot [DecidablePred (· ∈ K)] : U ⟶ invertedCylinder U K ε n :=
  embOfStd (partialCylinderEndpoint U K (!ε)) endpoint_notMem_std

@[simp] theorem endpointNot_apply [DecidablePred (· ∈ K)] (x : U) :
    endpointNot U K ε n x = partialCylinderEndpoint U K (!ε) x :=
  rfl

instance [DecidablePred (· ∈ K)] : IsInclusion (endpointNot U K ε n) :=
  inferInstanceAs (IsInclusion (embOfStd (partialCylinderEndpoint U K (!ε)) endpoint_notMem_std))

@[simp] theorem map_endpointNot [DecidablePred (· ∈ K)] (V : LowerSet U) :
    map (endpointNot U K ε n) V = copy K (!ε) V :=
  map_partialCylinderEndpoint (!ε) V

variable (U K ε) in
def endpointDual [DecidablePred (· ∈ K)] (hKd : ∀ z ∈ K, grade ℕ z < n) :
    dual U (topDim n) ⟶ invertedCylinder U K ε n :=
  ConcreteCategory.ofHom ⟨partialCylinderEndpointFun U K ε,
    IsMorphism.of_initialSeg (P := dual U (topDim n)) (Q := invertedCylinder U K ε n)
      (endpointInitialSeg U K ε) fun {x y} hxy => by
      have hc := (endpointInitialSeg U K ε).apply_covBy_apply_iff.2 hxy
      have hxyU : @CovBy U _ y x := hxy
      change (invertedCylinder U K ε n).orient hc = (dual U (topDim n)).orient hxy
      rw [orient_dual]
      by_cases hx : x ∈ K
      · have hy : y ∈ K := K.lower hxyU.le hx
        have hd : topDim n (grade ℕ x) = false := by simp [topDim, (hKd x hx).ne]
        rw [hd, Bool.false_xor]
        revert hc
        rw [show (endpointInitialSeg U K ε) x = mkK K x hx from endpointFun_of_mem ε hx,
          show (endpointInitialSeg U K ε) y = mkK K y hy from endpointFun_of_mem ε hy]
        intro hc
        exact U.orient_congr rfl rfl _ hxyU
      · by_cases hy : y ∈ K
        · revert hc
          rw [show (endpointInitialSeg U K ε) x = mkI K (some ε) x hx from
              endpointFun_of_notMem ε hx,
            show (endpointInitialSeg U K ε) y = mkK K y hy from endpointFun_of_mem ε hy]
          intro hc
          change (if ε = ε ∧ grade ℕ x = n then !U.orient hxyU else U.orient hxyU) = _
          by_cases hd : grade ℕ x = n
          · rw [if_pos ⟨rfl, hd⟩]; simp [topDim, hd]
          · rw [if_neg fun h => hd h.2]; simp [topDim, hd]
        · revert hc
          rw [show (endpointInitialSeg U K ε) x = mkI K (some ε) x hx from
              endpointFun_of_notMem ε hx,
            show (endpointInitialSeg U K ε) y = mkI K (some ε) y hy from
              endpointFun_of_notMem ε hy]
          intro hc
          change (if ε = ε ∧ grade ℕ x = n then !U.orient hxyU else U.orient hxyU) = _
          by_cases hd : grade ℕ x = n
          · rw [if_pos ⟨rfl, hd⟩]; simp [topDim, hd]
          · rw [if_neg fun h => hd h.2]; simp [topDim, hd]⟩

@[simp] theorem endpointDual_apply [DecidablePred (· ∈ K)] (hKd : ∀ z ∈ K, grade ℕ z < n)
    (x : dual U (topDim n)) :
    endpointDual U K ε hKd x = partialCylinderEndpoint U K ε x :=
  rfl

instance [DecidablePred (· ∈ K)] (hKd : ∀ z ∈ K, grade ℕ z < n) :
    IsInclusion (endpointDual U K ε hKd) :=
  ⟨(endpointInitialSeg U K ε).injective⟩

@[simp] theorem map_endpointDual [DecidablePred (· ∈ K)] (hKd : ∀ z ∈ K, grade ℕ z < n)
    (V : LowerSet (dual U (topDim n))) :
    map (endpointDual U K ε hKd) V = copy K ε V :=
  map_partialCylinderEndpoint (U := U) (K := K) ε V

theorem eq_mkI_none_of_mkI_some_covBy {β : Bool} (hx : x ∉ K) (hd : grade ℕ x = n)
    (hU : ∀ w : U, grade ℕ w ≤ n)
    {c : partialCylinder U K} (hc : mkI K (some β) x hx ⋖ c) :
    c = mkI K none x hx := by
  rcases covBy_mkI_some_cases hx hc with rfl | ⟨w, hw, hxw, rfl⟩
  · rfl
  · exfalso
    have h1 := grade_strictMono (𝕆 := ℕ) hxw.lt
    have h2 := hU w
    omega

theorem mkI_some_mem_facesIn_over_top {V : LowerSet U} (β : Bool) (hx : x ∉ K)
    (hd : grade ℕ x = n) (hU : ∀ w : U, grade ℕ w ≤ n) (hxV : x ∈ V) :
    mkI K (some β) x hx ∈ (invertedCylinder U K ε n).facesIn (over K V) n (!ε) := by
  simp only [facesIn, mem_ofPred_eq, SetLike.mem_coe, mem_over, proj_mkI, grade_mkI_some,
    disjoint_left]
  refine ⟨hxV, hd, fun c ⟨hcov, hor⟩ _ => ?_⟩
  obtain rfl := eq_mkI_none_of_mkI_some_covBy hx hd hU hcov
  rw [orient_mkI_none_mkI_some_top hx hd β hcov] at hor
  cases ε <;> simp at hor

theorem mkI_some_notMem_facesIn_over_top {V : LowerSet U} (β : Bool) (hx : x ∉ K)
    (hd : grade ℕ x = n) :
    mkI K (some β) x hx ∉ (invertedCylinder U K ε n).facesIn (over K V) n ε := by
  simp only [facesIn, mem_ofPred_eq, SetLike.mem_coe, mem_over, proj_mkI, grade_mkI_some,
    disjoint_left]
  rintro ⟨hxV, -, h⟩
  have hcov : mkI K (some β) x hx ⋖ mkI K none x hx := (covBy_mkI_some_mkI_none β hx hx).2 rfl
  exact h ⟨hcov, orient_mkI_none_mkI_some_top hx hd β hcov⟩ hxV

theorem proj_mem_boundary_of_maximal_over {V : LowerSet U} {e : ℕ} (α : Bool)
    {w : partialCylinder U K} (hw : Maximal (· ∈ over K V) w)
    (hd : grade ℕ w < e + 1) :
    partialCylinderProj U K w ∈ U.boundary V e α := by
  rcases w with ⟨a, ha⟩ | ⟨⟨_ | β⟩, ⟨a, ha⟩⟩
  · have hm := (mkK_maximal_over ha).1 hw
    have hd' : grade ℕ a < e + 1 := hd
    rcases Nat.lt_or_ge (grade ℕ a) e with h | h
    · exact subset_lowerClosure (Or.inr ⟨hm, h⟩)
    · have hae : grade ℕ a = e := by omega
      exact subset_lowerClosure (Or.inl (hae ▸ maximal_mem_iff_forall_mem_facesIn.1 hm α))
  · have hm := (mkI_none_maximal_over ha).1 hw
    have hd' : grade ℕ a + 1 < e + 1 := hd
    exact subset_lowerClosure (Or.inr ⟨hm, by change grade ℕ a < e; omega⟩)
  · exact (mkI_some_not_maximal_over β ha hw).elim

theorem maximal_of_mem_facesIn_of_mem_K {V : LowerSet U} {e : ℕ}
    (hU : ∀ w : U, grade ℕ w ≤ e + 1)
    (hKf : ∀ z ∈ K, ∀ w, grade ℕ w = e + 1 → ∀ h : z ⋖ w, U.orient h = ε) {g : U}
    (hg : g ∈ U.facesIn V e (!ε)) (hgK : g ∈ K) : Maximal (· ∈ V) g := by
  simp only [facesIn, mem_ofPred_eq, SetLike.mem_coe, disjoint_left, mem_cofaces,
    Bool.not_not] at hg
  obtain ⟨hgV, hgd, hno⟩ := hg
  refine ⟨hgV, fun c hc hgc => ?_⟩
  by_contra hne
  have hlt : g < c := lt_of_le_not_ge hgc hne
  have h1 := grade_strictMono (𝕆 := ℕ) hlt
  have h2 := hU c
  have hcov : g ⋖ c := GradeOrder.covBy_of_le_of_grade_eq_add_one hlt.le (by omega)
  exact hno ⟨hcov, hKf g hgK c (by omega) hcov⟩ hc

theorem mem_boundary_over_of_proj_le {V : LowerSet U} {j : ℕ} {α : Bool} {g : U}
    (hgK : g ∉ K) (hg : g ∈ U.facesIn V j (!α) ∪ {x | Maximal (· ∈ V) x ∧ grade ℕ x < j})
    {z : partialCylinder U K} (hzg : partialCylinderProj U K z ≤ g) :
    z ∈ (invertedCylinder U K ε n).boundary (over K V) (j + 1) α := by
  refine ((invertedCylinder U K ε n).boundary (over K V) (j + 1) α).lower
    (le_mkI_none_of_proj_le hgK hzg) (subset_lowerClosure ?_)
  rcases hg with hf | ⟨hm, hd⟩
  · obtain rfl : grade ℕ g = j := hf.2.1
    exact Or.inl ((mkI_none_mem_facesIn_over_iff hgK).2 hf)
  · exact Or.inr ⟨(mkI_none_maximal_over hgK).2 hm, by change grade ℕ g + 1 < j + 1; omega⟩

theorem boundary_over_top_eps {V : LowerSet U} {e : ℕ} (hU : ∀ w : U, grade ℕ w ≤ e + 1)
    (hKd : ∀ z ∈ K, grade ℕ z < e + 1)
    (hKf : ∀ z ∈ K, ∀ w, grade ℕ w = e + 1 → ∀ h : z ⋖ w, U.orient h = ε) :
    (invertedCylinder U K ε (e + 1)).boundary (over K V) (e + 1) ε =
      over K (U.boundary V e (!ε)) := by
  refine SetLike.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · obtain ⟨w, hw, hzw⟩ := mem_lowerClosure.1 hz
    refine mem_over.2 ((U.boundary V e (!ε)).lower (proj_le_proj hzw) ?_)
    rcases hw with hf | ⟨hm, hd⟩
    · rcases w with ⟨a, ha⟩ | ⟨⟨_ | β⟩, ⟨a, ha⟩⟩
      · have hd : grade ℕ a = e + 1 := hf.2.1
        have := hKd a ha
        omega
      · have hd : grade ℕ a + 1 = e + 1 := hf.2.1
        have hae : grade ℕ a = e := by omega
        exact subset_lowerClosure (Or.inl (hae ▸ (mkI_none_mem_facesIn_over_iff ha).1
          (hae.symm ▸ hf)))
      · have hd : grade ℕ a = e + 1 := hf.2.1
        exact (mkI_some_notMem_facesIn_over_top β ha hd hf).elim
    · exact proj_mem_boundary_of_maximal_over _ hm hd
  · obtain ⟨g, hg, hzg⟩ := mem_lowerClosure.1 (mem_over.1 hz)
    by_cases hgK : g ∈ K
    · have hzK : partialCylinderProj U K z ∈ K := K.lower hzg hgK
      have hgm : Maximal (· ∈ V) g := by
        rcases hg with hf | ⟨hm, -⟩
        · exact maximal_of_mem_facesIn_of_mem_K hU hKf hf hgK
        · exact hm
      have hdg : grade ℕ g < e + 1 := hKd g hgK
      have hle : z ≤ mkK K g hgK := by rw [eq_mkK_of_proj_mem hzK]; exact hzg
      exact ((invertedCylinder U K ε (e + 1)).boundary (over K V) (e + 1) ε).lower hle
        (subset_lowerClosure (Or.inr ⟨(mkK_maximal_over hgK).2 hgm, hdg⟩))
    · exact mem_boundary_over_of_proj_le hgK hg hzg

theorem boundary_over_top_not {V : LowerSet U} {e : ℕ} (hU : ∀ w : U, grade ℕ w ≤ e + 1)
    (hKd : ∀ z ∈ K, grade ℕ z < e + 1) :
    (invertedCylinder U K ε (e + 1)).boundary (over K V) (e + 1) (!ε) =
      copy K (!ε) V ⊔ copy K ε V ⊔ over K (U.boundary V e ε) := by
  classical
  have hcopy : ∀ β, copy K β V ≤
      (invertedCylinder U K ε (e + 1)).boundary (over K V) (e + 1) (!ε) := by
    intro β z hz
    obtain ⟨hzV, hze⟩ := mem_copy.1 hz
    obtain ⟨m, hym, hm⟩ := GradeOrder.exists_le_maximal (fun w _ => hU w) hzV
    have hmV : m ∈ V := hm.1
    by_cases hmK : m ∈ K
    · have hzK : partialCylinderProj U K z ∈ K := K.lower hym hmK
      have hle : z ≤ mkK K m hmK := by rw [eq_mkK_of_proj_mem hzK]; exact hym
      exact ((invertedCylinder U K ε (e + 1)).boundary (over K V) (e + 1) (!ε)).lower hle
        (subset_lowerClosure (Or.inr ⟨(mkK_maximal_over hmK).2 hm, hKd m hmK⟩))
    · have hdm : grade ℕ m ≤ e + 1 := hU m
      rcases Nat.lt_or_ge (grade ℕ m) (e + 1) with hlt | hge
      · rcases Nat.lt_or_ge (grade ℕ m) e with h | h
        · exact mem_boundary_over_of_proj_le hmK (Or.inr ⟨hm, h⟩) hym
        · have hme : grade ℕ m = e := by omega
          exact mem_boundary_over_of_proj_le hmK
            (Or.inl (hme ▸ maximal_mem_iff_forall_mem_facesIn.1 hm _)) hym
      · have hdm' : grade ℕ m = e + 1 := by omega
        refine ((invertedCylinder U K ε (e + 1)).boundary (over K V) (e + 1) (!ε)).lower ?_
          (subset_lowerClosure (Or.inl (mkI_some_mem_facesIn_over_top β hmK hdm' hU hmV)))
        rw [← hze, ← endpoint_of_notMem β hmK]
        exact (isMorphism (partialCylinderEndpoint U K β)).monotone hym
  refine SetLike.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · obtain ⟨w, hw, hzw⟩ := mem_lowerClosure.1 hz
    rcases hw with hf | ⟨hm, hd⟩
    · rcases w with ⟨a, ha⟩ | ⟨⟨_ | β⟩, ⟨a, ha⟩⟩
      · have hd : grade ℕ a = e + 1 := hf.2.1
        have := hKd a ha
        omega
      · have hd : grade ℕ a + 1 = e + 1 := hf.2.1
        have hae : grade ℕ a = e := by omega
        have hf' := (mkI_none_mem_facesIn_over_iff ha).1 (hae.symm ▸ hf)
        rw [Bool.not_not] at hf'
        exact Or.inr (mem_over.2 ((U.boundary V e ε).lower (proj_le_proj hzw)
          (subset_lowerClosure (Or.inl (hae ▸ hf')))))
      · have haV : a ∈ V := mem_over.1 hf.1
        have hzc : z ∈ copy K β V := by
          refine copy_mono β (LowerSet.Iic_le.2 haV) ?_
          rw [← Iic_endpoint, endpoint_of_notMem β ha]
          exact hzw
        by_cases hβ : β = ε
        · subst hβ; exact Or.inl (Or.inr hzc)
        · obtain rfl := Bool.eq_not_of_ne hβ; exact Or.inl (Or.inl hzc)
    · exact Or.inr (mem_over.2 ((U.boundary V e ε).lower (proj_le_proj hzw)
        (proj_mem_boundary_of_maximal_over _ hm hd)))
  · rcases hz with (hz | hz) | hz
    · exact hcopy (!ε) hz
    · exact hcopy ε hz
    · obtain ⟨g, hg, hzg⟩ := mem_lowerClosure.1 (mem_over.1 hz)
      by_cases hgK : g ∈ K
      · have hzK : partialCylinderProj U K z ∈ K := K.lower hzg hgK
        refine hcopy (!ε) ?_
        rw [eq_mkK_of_proj_mem hzK]
        exact (mkK_mem_copy hzK).2
          (boundary_le V e ε ((U.boundary V e ε).lower hzg (subset_lowerClosure hg)))
      · refine mem_boundary_over_of_proj_le hgK ?_ hzg
        rwa [Bool.not_not]

theorem dimension_le_of_changed {c : partialCylinder U K}
    (hc : changed ε n c = true) : n ≤ grade ℕ c := by
  rcases c with ⟨a, ha⟩ | ⟨⟨_ | β⟩, ⟨a, ha⟩⟩
  · simp [changed] at hc
  · have hd : n ≤ grade ℕ a := by simpa [changed] using hc
    change n ≤ grade ℕ a + 1
    omega
  · have hd : β = ε ∧ n ≤ grade ℕ a := by simpa [changed] using hc
    exact hd.2

theorem changed_eq_false_of_dim_lt {c : partialCylinder U K}
    (hc : grade ℕ c < n) : changed ε n c = false := by
  cases h : changed ε n c
  · rfl
  · have := dimension_le_of_changed h; omega

theorem boundary_eq_of_add_two_le {j : ℕ} (hj : j + 2 ≤ n)
    (S : LowerSet (partialCylinder U K)) (α : Bool) :
    (invertedCylinder U K ε n).boundary S j α = (partialCylinder U K).boundary S j α := by
  refine SetLike.ext fun z => ?_
  simp only [boundary, mem_lowerClosure]
  refine exists_congr fun w => and_congr (or_congr ?_ Iff.rfl) Iff.rfl
  refine ⟨fun hf => (mem_facesIn_iff_of_orient_eq fun c _ hc => ?_).1 hf,
    fun hf => (mem_facesIn_iff_of_orient_eq fun c _ hc => ?_).2 hf⟩
  · refine orient_eq_of_changed_eq_false (changed_eq_false_of_dim_lt ?_) hc
    have := Nat.covBy_iff_add_one_eq.1 (hc.grade ℕ)
    have hd' : grade ℕ w = j := hf.2.1
    omega
  · refine orient_eq_of_changed_eq_false (changed_eq_false_of_dim_lt ?_) hc
    have := Nat.covBy_iff_add_one_eq.1 (hc.grade ℕ)
    have hd' : grade ℕ w = j := hf.2.1
    omega

theorem orient_mkI_some_mkI_some_top {β : Bool} {c a : U} (hc : c ∉ K) (ha : a ∉ K)
    (hd : grade ℕ c = n) (h : a ⋖ c)
    (hcov : mkI K (some β) a ha ⋖ mkI K (some β) c hc) :
    (invertedCylinder U K ε n).orient hcov = xor (decide (β = ε)) (U.orient h) := by
  change (if β = ε ∧ grade ℕ c = n then !U.orient h else U.orient h) = _
  by_cases hβ : β = ε
  · rw [if_pos ⟨hβ, hd⟩]; simp [hβ, xor]
  · rw [if_neg fun h' => hβ h'.1]; simp [hβ, xor]

theorem mkI_some_mem_facesIn_over_sub {V : LowerSet U} {e : ℕ} {α β : Bool} (hx : x ∉ K)
    (hd : grade ℕ x = e) :
    mkI K (some β) x hx ∈ (invertedCylinder U K ε (e + 1)).facesIn (over K V) e α ↔
      β = α ∧ x ∈ U.facesIn V e (!ε) := by
  have hnt : grade ℕ x ≠ e + 1 := by omega
  have h1 (hc : mkI K (some β) x hx ⋖ mkI K none x hx) :
      (invertedCylinder U K ε (e + 1)).orient hc = β := by
    change (if grade ℕ x = e + 1 then !ε else β) = β
    rw [if_neg hnt]
  simp only [facesIn, mem_ofPred_eq, SetLike.mem_coe, mem_over, proj_mkI, grade_mkI_some,
    disjoint_left]
  constructor
  · rintro ⟨hxV, _, hno⟩
    have hβα : β = α := by
      by_contra hne
      have hc : mkI K (some β) x hx ⋖ mkI K none x hx := (covBy_mkI_some_mkI_none β hx hx).2 rfl
      refine hno ⟨hc, ?_⟩ hxV
      rw [h1 hc]
      cases α <;> cases β <;> simp at hne ⊢
    subst hβα
    refine ⟨rfl, hxV, hd, fun c ⟨hcov, hor⟩ hcV => ?_⟩
    rw [Bool.not_not] at hor
    have hcK : c ∉ K := fun h => hx (K.lower hcov.le h)
    have hdc : grade ℕ c = e + 1 := by
      have := Nat.covBy_iff_add_one_eq.1 (hcov.grade ℕ)
      omega
    have hc' : mkI K (some β) x hx ⋖ mkI K (some β) c hcK :=
      (covBy_mkI_some_mkI_some β β hx hcK).2 ⟨rfl, hcov⟩
    refine hno ⟨hc', ?_⟩ hcV
    rw [orient_mkI_some_mkI_some_top hcK hx hdc hcov hc', hor]
    cases β <;> cases ε <;> simp
  · rintro ⟨rfl, hxV, _, hno⟩
    refine ⟨hxV, hd, fun c ⟨hcov, hor⟩ hcV => ?_⟩
    rcases covBy_mkI_some_cases hx hcov with rfl | ⟨w, hw, hxw, rfl⟩
    · rw [h1 hcov] at hor; cases β <;> simp at hor
    · have hdw : grade ℕ w = e + 1 := by
        have := Nat.covBy_iff_add_one_eq.1 (hxw.grade ℕ)
        omega
      rw [orient_mkI_some_mkI_some_top hw hx hdw hxw hcov] at hor
      refine hno ⟨hxw, ?_⟩ hcV
      revert hor; cases β <;> cases ε <;> cases U.orient hxw <;> simp

theorem mkK_mem_facesIn_over_sub {V : LowerSet U} {e : ℕ} {α : Bool} (hx : x ∈ K)
    (hd : grade ℕ x = e) (hU : ∀ w : U, grade ℕ w ≤ e + 1)
    (hKd : ∀ z ∈ K, grade ℕ z < e + 1)
    (hKf : ∀ z ∈ K, ∀ w, grade ℕ w = e + 1 → ∀ h : z ⋖ w, U.orient h = ε) :
    mkK K x hx ∈ (invertedCylinder U K ε (e + 1)).facesIn (over K V) e α ↔ Maximal (· ∈ V) x := by
  constructor
  · simp only [facesIn, mem_ofPred_eq, SetLike.mem_coe, mem_over, proj_mkK, grade_mkK,
      disjoint_left]
    rintro ⟨hxV, -, hno⟩
    refine ⟨hxV, fun c hc hxc => ?_⟩
    by_contra hne
    have hlt : x < c := lt_of_le_not_ge hxc hne
    have h1 := grade_strictMono (𝕆 := ℕ) hlt
    have h2 := hU c
    have hcov : x ⋖ c := GradeOrder.covBy_of_le_of_grade_eq_add_one hlt.le (by omega)
    have hdc : grade ℕ c = e + 1 := by omega
    have hcK : c ∉ K := fun h => by have := hKd c h; omega
    have hor := hKf x hx c hdc hcov
    by_cases hα : α = ε
    · have hc' : mkK K x hx ⋖ mkI K (some ε) c hcK := (covBy_mkK_mkI_some hx ε hcK).2 hcov
      refine hno ⟨hc', ?_⟩ hc
      rw [orient_mkI_some_top hcK hdc hc' hcov, hα]
      exact congrArg (!·) hor
    · have hc' : mkK K x hx ⋖ mkI K (some (!ε)) c hcK := (covBy_mkK_mkI_some hx (!ε) hcK).2 hcov
      refine hno ⟨hc', ?_⟩ hc
      rw [orient_eq_of_changed_eq_false (mkI_some_notMem_std hcK) hc',
        orient_mkI_some (!ε) hcK hc' hcov]
      exact hor.trans (Bool.eq_not_of_ne (Ne.symm hα))
  · intro hm
    have h := (maximal_mem_iff_forall_mem_facesIn (P := invertedCylinder U K ε (e + 1))).1
      ((mkK_maximal_over hx).2 hm) α
    rwa [grade_mkK, hd] at h

theorem boundary_over_sub {V : LowerSet U} {f : ℕ} (hg : U.IsGlobular V)
    (hU : ∀ w : U, grade ℕ w ≤ f + 2) (hKd : ∀ z ∈ K, grade ℕ z < f + 2)
    (hKf : ∀ z ∈ K, ∀ w, grade ℕ w = f + 2 → ∀ h : z ⋖ w, U.orient h = ε) (α : Bool) :
    (invertedCylinder U K ε (f + 2)).boundary (over K V) (f + 1) α =
      copy K α (U.boundary V (f + 1) (!ε)) ⊔ over K (U.boundary V f (!α)) := by
  classical
  set D := U.boundary V (f + 1) (!ε)
  have hcopy : copy K α D ≤ (invertedCylinder U K ε (f + 2)).boundary (over K V) (f + 1) α := by
    intro z hz
    obtain ⟨hyD, hze⟩ := mem_copy.1 hz
    obtain ⟨g, hg', hyg⟩ := mem_lowerClosure.1 hyD
    have hle : ∀ (hgK : g ∈ K), z ≤ mkK K g hgK := fun hgK => by
      rw [eq_mkK_of_proj_mem (K.lower hyg hgK)]; exact hyg
    rcases hg' with hf | ⟨hm, hd⟩
    · have hd : grade ℕ g = f + 1 := hf.2.1
      by_cases hgK : g ∈ K
      · refine ((invertedCylinder U K ε (f + 2)).boundary (over K V) (f + 1) α).lower
          (hle hgK) (subset_lowerClosure (Or.inl ?_))
        exact (mkK_mem_facesIn_over_sub hgK hd hU hKd hKf).2
          (maximal_of_mem_facesIn_of_mem_K hU hKf hf hgK)
      · refine ((invertedCylinder U K ε (f + 2)).boundary (over K V) (f + 1) α).lower ?_
          (subset_lowerClosure (Or.inl ((mkI_some_mem_facesIn_over_sub hgK hd).2 ⟨rfl, hf⟩)))
        rw [← hze, ← endpoint_of_notMem α hgK]
        exact (isMorphism (partialCylinderEndpoint U K α)).monotone hyg
    · by_cases hgK : g ∈ K
      · exact ((invertedCylinder U K ε (f + 2)).boundary (over K V) (f + 1) α).lower (hle hgK)
          (subset_lowerClosure (Or.inr ⟨(mkK_maximal_over hgK).2 hm, hd⟩))
      · rcases Nat.lt_or_ge (grade ℕ g) f with h | h
        · exact mem_boundary_over_of_proj_le hgK (Or.inr ⟨hm, h⟩) hyg
        · have hgf : grade ℕ g = f := by omega
          exact mem_boundary_over_of_proj_le hgK
            (Or.inl (hgf ▸ maximal_mem_iff_forall_mem_facesIn.1 hm _)) hyg
  refine SetLike.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · obtain ⟨w, hw, hzw⟩ := mem_lowerClosure.1 hz
    rcases hw with hf | ⟨hm, hd⟩
    · rcases w with ⟨a, ha⟩ | ⟨⟨_ | β⟩, ⟨a, ha⟩⟩
      · have hd : grade ℕ a = f + 1 := hf.2.1
        have hm := (mkK_mem_facesIn_over_sub ha hd hU hKd hKf).1 hf
        have haD : a ∈ D :=
          subset_lowerClosure (Or.inl (hd ▸ maximal_mem_iff_forall_mem_facesIn.1 hm _))
        obtain ⟨b, hb, rfl⟩ := exists_eq_mkK_of_le_mkK ha hzw
        exact Or.inl ((mkK_mem_copy hb).2 (D.lower hzw haD))
      · have hd : grade ℕ a + 1 = f + 1 := hf.2.1
        have haf : grade ℕ a = f := by omega
        refine Or.inr (mem_over.2 ((U.boundary V f (!α)).lower (proj_le_proj hzw) ?_))
        exact subset_lowerClosure (Or.inl (haf ▸ (mkI_none_mem_facesIn_over_iff ha).1
          (haf.symm ▸ hf)))
      · have hd : grade ℕ a = f + 1 := hf.2.1
        obtain ⟨rfl, hf'⟩ := (mkI_some_mem_facesIn_over_sub ha hd).1 hf
        have haD : a ∈ D := subset_lowerClosure (Or.inl hf')
        refine Or.inl (copy_mono β (LowerSet.Iic_le.2 haD) ?_)
        rw [← Iic_endpoint, endpoint_of_notMem β ha]
        exact hzw
    · exact Or.inr (mem_over.2 ((U.boundary V f (!α)).lower (proj_le_proj hzw)
        (proj_mem_boundary_of_maximal_over _ hm hd)))
  · rcases hz with hz | hz
    · exact hcopy hz
    · have hpz := mem_over.1 hz
      by_cases hzK : partialCylinderProj U K z ∈ K
      · refine hcopy ?_
        rw [eq_mkK_of_proj_mem hzK]
        exact (mkK_mem_copy hzK).2 (hg.boundary_le_boundary (Nat.lt_succ_self f) _ _ hpz)
      · obtain ⟨g, hg', hzg⟩ := mem_lowerClosure.1 hpz
        have hgK : g ∉ K := fun h => hzK (K.lower hzg h)
        exact mem_boundary_over_of_proj_le hgK hg' hzg

theorem boundary_over_eq_boundary_over_bdry {V : LowerSet U} {e j : ℕ}
    (hg : U.IsGlobular V) (hU : ∀ w : U, grade ℕ w ≤ e + 1) (hj : j ≤ e) (hj0 : 0 < j)
    (hKd : ∀ z ∈ K, grade ℕ z < e + 1)
    (hKf : ∀ z ∈ K, ∀ w, grade ℕ w = e + 1 → ∀ h : z ⋖ w, U.orient h = ε) (α : Bool) :
    (invertedCylinder U K ε (e + 1)).boundary (over K V) j α =
      (partialCylinder U K).boundary (over K (U.boundary V e (!ε))) j α := by
  have gD := hg.boundary e (!ε)
  rcases Nat.lt_or_ge j e with hje | hje
  · rw [boundary_eq_of_add_two_le (by omega), boundary_over_boundary hg,
      boundary_over_boundary gD, hg j e hje]
  · obtain rfl : j = e := le_antisymm hj hje
    obtain ⟨f, rfl⟩ : ∃ f, j = f + 1 := ⟨j - 1, by omega⟩
    rw [boundary_over_sub hg hU hKd hKf, boundary_over_succ gD,
      boundary_eq_self (krullDim_boundary_le V (f + 1) (!ε)),
      hg f (f + 1) (Nat.lt_succ_self f)]

theorem dim_lt_of_mem_K {e : ℕ}
    (hKU : K ≤ U.boundary ⊤ e ε) : ∀ z ∈ K, grade ℕ z < e + 1 :=
  fun _ hz => Nat.lt_succ_of_le (grade_le_of_mem_boundary (hKU hz))

theorem orient_eq_of_mem_K {e : ℕ}
    (hKU : K ≤ U.boundary ⊤ e ε) :
    ∀ z ∈ K, ∀ w, grade ℕ w = e + 1 → ∀ h : z ⋖ w, U.orient h = ε := by
  intro z hz w hw hcov
  have hdz : grade ℕ z = e := by
    have := Nat.covBy_iff_add_one_eq.1 (hcov.grade ℕ)
    omega
  have hf := mem_facesIn_of_mem_boundary (hKU hz) hdz
  simp only [facesIn, mem_ofPred_eq, LowerSet.coe_top, mem_univ, true_and, disjoint_left,
    mem_cofaces] at hf
  by_contra h
  exact hf.2 ⟨hcov, Bool.eq_not_of_ne h⟩ trivial

theorem subset_std_of_dimOf_lt {S : LowerSet (partialCylinder U K)}
    (h : krullDim S < (n : WithBot ℕ∞)) : S ≤ std K ε n := fun z hz => by
  refine mem_std_of_dim_lt (lt_of_le_of_lt (grade_proj_le z) ?_)
  have h1 : (grade ℕ z : WithBot ℕ∞) < (n : WithBot ℕ∞) :=
    lt_of_le_of_lt (grade_le_krullDim (⟨z, hz⟩ : S)) h
  exact_mod_cast h1

variable (K ε n) in
theorem embOfEmb_mem_std {B : OGP.{u}} (L : LowerSet B) (ι : B ⟶ U) [IsInclusion ι]
    (hι : ∀ x, ι x ∈ K ↔ x ∈ L) (hd : ∀ x, grade ℕ (ι x) < n)
    (a : partialCylinder B L) :
    PartialCylinder.embOfEmb K L ι hι a ∈ std K ε n :=
  mem_std_of_dim_lt ((PartialCylinder.proj_carrierMapOfMap K L ι hι a).symm ▸ hd _)

theorem boundary_copy_of_ne {β : Bool} (hβ : β ≠ ε) (V : LowerSet U) (k : ℕ) (α : Bool) :
    (invertedCylinder U K ε n).boundary (copy K β V) k α = copy K β (U.boundary V k α) := by
  classical
  obtain rfl : β = !ε := Bool.eq_not_of_ne hβ
  rw [← map_endpointNot (n := n), ← map_boundary, map_endpointNot]

theorem boundary_copy_eps {e : ℕ}
    (hKd : ∀ z ∈ K, grade ℕ z < e + 1) (V : LowerSet U) (α : Bool) :
    (invertedCylinder U K ε (e + 1)).boundary (copy K ε V) e α =
      copy K ε (U.boundary V e (!α)) := by
  classical
  have h := boundary_dual (P := U) (topDim (e + 1)) V e α
  rw [show topDim (e + 1) (e + 1) = true by simp [topDim], Bool.true_xor] at h
  rw [← h, ← map_endpointDual (ε := ε) hKd, ← map_boundary, map_endpointDual]

theorem isPastingIn_copy_copy {e : ℕ} (hU : ∀ w : U, grade ℕ w ≤ e + 1)
    (hKU : K = U.boundary ⊤ e ε) :
    (invertedCylinder U K ε (e + 1)).IsPastingIn e (copy K false ⊤) (copy K true ⊤)
      ((invertedCylinder U K ε (e + 1)).boundary ⊤ (e + 1) (!ε)) := by
  have hKd : ∀ z ∈ K, grade ℕ z < e + 1 := dim_lt_of_mem_K hKU.le
  have hK' : ∀ β, copy K β (U.boundary ⊤ e ε) = over K (K ⊓ ⊤) := by
    intro β
    rw [inf_top_eq, ← hKU]
    exact (over_eq_copy_of_le le_rfl β).symm
  have hint : copy K false ⊤ ⊓ copy K true ⊤ = over K (K ⊓ ⊤) := by
    rw [over_eq_copy_of_le inf_le_left false]
    simpa only [inf_idem, top_inf_eq, inf_top_eq, Bool.not_false]
      using copy_inf_copy_not (K := K) false ⊤ ⊤
  refine ⟨?_, ?_, ?_⟩
  · rw [← over_top (K := K), boundary_over_top_not hU hKd, ← hKU]
    have hsub : over K K ≤ copy K ε ⊤ := by
      rw [over_eq_copy_of_le le_rfl ε]
      exact copy_mono ε le_top
    rw [sup_eq_left.2 (hsub.trans le_sup_right)]
    cases ε
    · exact sup_comm _ _
    · rfl
  · rw [hint]
    cases ε
    · rw [boundary_copy_eps hKd, Bool.not_true, hK']
    · rw [boundary_copy_of_ne (by decide), hK']
  · rw [hint]
    cases ε
    · rw [boundary_copy_of_ne (by decide), hK']
    · rw [boundary_copy_eps hKd, Bool.not_false, hK']

end InvertedCylinder

end Atoms.Molecule.OGP
