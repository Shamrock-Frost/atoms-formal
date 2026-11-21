import Atoms.Molecule.Cylinder.Partial

universe u

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

namespace PartialCylinder

variable {U : OGP.{u}} {K : LowerSet U} {x y : U}

theorem endpoint_mem_cofaces [DecidablePred (· ∈ K)] (β : Bool) {γ : Bool}
    (h : y ∈ U.cofaces γ x) :
    partialCylinderEndpoint U K β y ∈
      (partialCylinder U K).cofaces γ (partialCylinderEndpoint U K β x) :=
  ((isMorphism (partialCylinderEndpoint U K β)).bijOn_faces y γ).mapsTo h

theorem mkI_none_mem_cofaces_mkI_none {γ : Bool} (hx : x ∉ K) (hy : y ∉ K)
    (h : y ∈ U.cofaces γ x) :
    mkI K none y hy ∈ (partialCylinder U K).cofaces (!γ) (mkI K none x hx) := by
  obtain ⟨hcov, hor⟩ := h
  refine ⟨(covBy_mkI_none_mkI_none hx hy).2 hcov, ?_⟩
  change (!U.orient _) = !γ
  rw [U.orient_congr rfl rfl _ hcov, hor]

theorem mkI_none_mem_cofaces_mkI_some (γ : Bool) (hx : x ∉ K) :
    mkI K none x hx ∈ (partialCylinder U K).cofaces γ (mkI K (some γ) x hx) :=
  ⟨(covBy_mkI_some_mkI_none γ hx hx).2 rfl, orient_mkI_none_mkI_some γ hx _⟩

section Globular

variable {V : LowerSet U}

theorem boundary_over_le_boundary_over_of_lt (hg : U.IsGlobular V) {k n : ℕ} (hkn : k < n)
    (α β : Bool) :
    (partialCylinder U K).boundary (over K V) k α ≤
      (partialCylinder U K).boundary (over K V) n β := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro z hz
  rw [boundary_over_succ hg]
  rcases mem_copy_or_mem_over_of_mem_boundary_over hz with h | ⟨hk0, h⟩
  · by_cases hαβ : α = β
    · subst hαβ
      exact Or.inl (copy_mono α (hg.boundary_le_boundary hkn α α) h)
    · have hβ : (!β) = α := Bool.not_eq.2 (Ne.symm hαβ)
      refine Or.inr (over_mono ?_ (copy_le_over α _ h))
      rw [hβ]
      rcases (Nat.le_of_lt_succ hkn).eq_or_lt with rfl | hlt
      · exact le_rfl
      · exact hg.boundary_le_boundary hlt α α
  · exact Or.inr (over_mono (hg.boundary_le_boundary (by omega) (!α) (!β)) h)

theorem mem_facesIn_boundary_over_iff (hg : U.IsGlobular V) {k n : ℕ} (hkn : k < n) (α β : Bool)
    {z : partialCylinder U K} :
    z ∈ (partialCylinder U K).facesIn ((partialCylinder U K).boundary (over K V) n β) k α ↔
      z ∈ (partialCylinder U K).facesIn (over K V) k α := by
  classical
  constructor
  swap
  · intro hf
    exact mem_facesIn_of_subset (boundary_le (over K V) n β) hf
      (boundary_over_le_boundary_over_of_lt hg hkn α β (mem_boundary_of_mem_facesIn hf le_rfl))
  intro hf
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hzZ, hd, hno⟩ := hf
  rw [boundary_over_succ hg] at hzZ hno
  set S := U.boundary V (m + 1) β
  set T := U.boundary V m (!β)
  have hTS : T ≤ S := hg.boundary_le_boundary (Nat.lt_succ_self m) (!β) β
  have hcS : copy K β S ≤ copy K β S ⊔ over K T := le_sup_left
  have hcT : over K T ≤ copy K β S ⊔ over K T := le_sup_right
  have hSV : ∀ {w : U} {d : ℕ} {γ : Bool}, d < m + 1 → w ∈ U.facesIn S d γ →
      w ∈ U.facesIn V d γ := fun {w d γ} hw hfw => by
    rwa [facesIn_eq_of_boundary_eq (hg d (m + 1) hw γ β)] at hfw
  have hTV : ∀ {w : U} {d : ℕ} {γ : Bool}, d < m → w ∈ U.facesIn T d γ →
      w ∈ U.facesIn V d γ := fun {w d γ} hw hfw => by
    rwa [facesIn_eq_of_boundary_eq (hg d m hw γ (!β))] at hfw
  have hZ {b : partialCylinder U K} (hb : b ∈ (partialCylinder U K).cofaces (!α) z) :
      b ∉ copy K β S ⊔ over K T := fun hb' => disjoint_left.1 hno hb hb'
  rcases z with ⟨x, hx⟩ | ⟨⟨_ | γ⟩, ⟨x, hx⟩⟩
  · have hxS : x ∈ S := hzZ.elim (fun h => (mkK_mem_copy hx).1 h) fun h => hTS (mem_over.1 h)
    have hdx : grade ℕ x = k := hd
    refine (mkK_mem_facesIn_over hx).2 (hSV (by omega) ⟨hxS, hdx, disjoint_left.2 fun w hcof hwS =>
      hZ ?_ (hcS (by rw [← map_partialCylinderEndpoint]; exact ⟨w, hwS, rfl⟩))⟩)
    have := endpoint_mem_cofaces (K := K) β hcof
    rwa [endpoint_of_mem β hx] at this
  · have hxT : x ∈ T := hzZ.elim (fun h => (mkI_none_notMem_copy hx h).elim) mem_over.1
    have hdx : grade ℕ x + 1 = k := hd
    rw [← hdx]
    refine (mkI_none_mem_facesIn_over hx).2 (hTV (by omega)
      ⟨hxT, rfl, disjoint_left.2 fun w hcof hwT => ?_⟩)
    have hw : w ∉ K := fun h => hx (K.lower hcof.1.le h)
    have := mkI_none_mem_cofaces_mkI_none (K := K) hx hw hcof
    rw [Bool.not_not] at this
    exact hZ this (hcT ((mem_over (a := mkI K none w hw)).2 hwT))
  · have hdx : grade ℕ x = k := hd
    by_cases hxT : x ∈ T
    · have hγ : γ = α := by
        by_contra hne
        obtain rfl : γ = !α := Bool.eq_not_of_ne hne
        exact hZ (mkI_none_mem_cofaces_mkI_some (!α) hx)
          (hcT ((mem_over (a := mkI K none x hx)).2 hxT))
      subst hγ
      refine (mkI_some_mem_facesIn_over hx).2 ⟨rfl, ?_⟩
      by_cases hαβ : γ = β
      · subst hαβ
        refine hSV (by omega) ⟨hTS hxT, hdx, disjoint_left.2 fun w hcof hwS =>
          hZ ?_ (hcS (by rw [← map_partialCylinderEndpoint]; exact ⟨w, hwS, rfl⟩))⟩
        have := endpoint_mem_cofaces (K := K) γ hcof
        rwa [endpoint_of_notMem γ hx] at this
      · have hβ : (!β) = γ := Bool.not_eq.2 (Ne.symm hαβ)
        have hfT : x ∈ U.facesIn T k γ := by
          refine ⟨hxT, hdx, disjoint_left.2 fun w hcof hwT => ?_⟩
          have hw : w ∉ K := fun h => hx (K.lower hcof.1.le h)
          have := endpoint_mem_cofaces (K := K) γ hcof
          rw [endpoint_of_notMem γ hx, endpoint_of_notMem γ hw] at this
          exact hZ this (hcT ((mem_over (a := mkI K (some γ) w hw)).2 hwT))
        rcases Nat.lt_or_ge k m with hkm | hkm
        · exact hTV hkm hfT
        · obtain rfl : k = m := by omega
          have hxT' : x ∈ U.boundary V k γ := by rwa [← hβ]
          exact mem_facesIn_of_mem_boundary hxT' hdx
    · have hxS : γ = β ∧ x ∈ S :=
        hzZ.elim (mkI_some_mem_copy hx).1 fun h => (hxT (mem_over.1 h)).elim
      obtain ⟨rfl, hxS⟩ := hxS
      have hfV : x ∈ U.facesIn V k α := by
        refine hSV (by omega) ⟨hxS, hdx, disjoint_left.2 fun w hcof hwS =>
          hZ ?_ (hcS (by rw [← map_partialCylinderEndpoint]; exact ⟨w, hwS, rfl⟩))⟩
        have := endpoint_mem_cofaces (K := K) γ hcof
        rwa [endpoint_of_notMem γ hx] at this
      refine (mkI_some_mem_facesIn_over hx).2 ⟨?_, hfV⟩
      by_contra hne
      obtain rfl : α = !γ := Bool.eq_not_of_ne (Ne.symm hne)
      refine hxT ?_
      have hmem := mem_boundary_of_mem_facesIn hfV le_rfl
      rcases (Nat.le_of_lt_succ hkn).eq_or_lt with rfl | hlt
      · exact hmem
      · exact hg.boundary_le_boundary hlt (!γ) (!γ) hmem

theorem isGlobular_over (hg : U.IsGlobular V) :
    (partialCylinder U K).IsGlobular (over K V) := by
  intro k n hk α β
  refine boundary_congr (Set.ext fun z => ?_) fun z hz => ?_
  · exact mem_facesIn_boundary_over_iff hg hk α β
  · exact maximal_mem_boundary_iff_of_grade_lt (hz.trans hk)

theorem isRound_over (hr : U.IsRound V) (hKV : K ⊓ V ≤ U.bdryFull V) :
    (partialCylinder U K).IsRound (over K V) where
  isGlobular := isGlobular_over hr.isGlobular
  inf_boundary_zero _ := by
    rw [boundary_over_zero, boundary_over_zero,
      show (true : Bool) = !false from rfl, copy_inf_copy_not false, Bool.not_false,
      copy_eq_bot_iff, ← le_bot_iff]
    by_cases hV0 : 0 < krullDim V
    · rw [hr.inf_boundary_zero hV0, bot_inf_eq]
    · refine (le_inf inf_le_right
        (inf_le_left.trans (inf_le_left.trans (boundary_le V 0 false)))).trans (hKV.trans ?_)
      rw [bdryFull, bdry_eq_bot (not_lt.1 hV0), bdry_eq_bot (not_lt.1 hV0), sup_bot_eq]
  inf_boundary_succ m hm := by
    have hg := hr.isGlobular
    have gX := isGlobular_over (K := K) hg
    have hmV : (m : WithBot ℕ∞) < krullDim V :=
      not_le.1 fun hle => hm.not_ge (krullDim_over_le hle)
    refine le_antisymm (fun z hz => ?_)
      (sup_le (le_inf (gX.boundary_le_boundary (Nat.lt_succ_self m) _ _)
          (gX.boundary_le_boundary (Nat.lt_succ_self m) _ _))
        (le_inf (gX.boundary_le_boundary (Nat.lt_succ_self m) _ _)
          (gX.boundary_le_boundary (Nat.lt_succ_self m) _ _)))
    have hz' (δ : Bool) :
        z ∈ copy K δ (U.boundary V (m + 1) δ) ⊔ over K (U.boundary V m (!δ)) := by
      rw [← boundary_over_succ hg]
      cases δ
      exacts [hz.1, hz.2]
    have hc (δ : Bool) :
        copy K δ (U.boundary V m δ) ≤ (partialCylinder U K).boundaryFull (over K V) m :=
      (copy_boundary_le_boundary_over V m δ).trans
        (by cases δ; exacts [le_sup_left, le_sup_right])
    rcases z with ⟨x, hx⟩ | ⟨⟨_ | γ⟩, ⟨x, hx⟩⟩
    · have hxb (δ : Bool) : x ∈ U.boundary V (m + 1) δ :=
        (hz' δ).elim (mkK_mem_copy hx).1 fun h =>
          hg.boundary_le_boundary (Nat.lt_succ_self m) (!δ) δ (mem_over.1 h)
      have hx' : x ∈ U.boundaryFull V m := by
        by_cases hlt : ((m + 1 : ℕ) : WithBot ℕ∞) < krullDim V
        · rw [← hr.inf_boundary_succ m hlt]
          exact ⟨hxb false, hxb true⟩
        · have hd : krullDim V = ((m + 1 : ℕ) : WithBot ℕ∞) := by
            obtain ⟨⟨x₀, hx₀⟩, hx₀m⟩ := coe_lt_krullDim_iff.1 hmV
            refine le_antisymm (not_lt.1 hlt) ?_
            have hm' : m + 1 ≤ grade ℕ x₀ := by exact_mod_cast hx₀m
            exact (by exact_mod_cast hm' : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ grade ℕ x₀).trans
              (grade_le_krullDim (⟨x₀, hx₀⟩ : V))
          have hmem := hKV ⟨hx, boundary_le V _ _ (hxb true)⟩
          rwa [bdryFull, bdry_eq_boundary hd, bdry_eq_boundary hd] at hmem
      exact hx'.elim (fun h => hc false ((mkK_mem_copy hx).2 h))
        fun h => hc true ((mkK_mem_copy hx).2 h)
    · have hxb (δ : Bool) : x ∈ U.boundary V m (!δ) :=
        (hz' δ).elim (fun h => (mkI_none_notMem_copy hx h).elim) mem_over.1
      rcases m with _ | m
      · have h0 : x ∈ (⊥ : LowerSet U) :=
          hr.inf_boundary_zero hmV ▸ ⟨hxb true, hxb false⟩
        exact h0.elim
      · have hm' : x ∈ U.boundaryFull V m :=
          hr.inf_boundary_succ m hmV ▸ ⟨hxb true, hxb false⟩
        have hov (δ : Bool) (h : x ∈ U.boundary V m δ) :
            mkI K none x hx ∈ (partialCylinder U K).boundaryFull (over K V) (m + 1) := by
          have h1 := over_boundary_le_boundary_over (K := K) hg m (!δ)
            ((mem_over (a := mkI K none x hx)).2 (by rwa [Bool.not_not]))
          cases δ
          exacts [Or.inr h1, Or.inl h1]
        exact hm'.elim (hov false) (hov true)
    · have h : x ∈ U.boundary V m γ := by
        rcases hz' (!γ) with h | h
        · exact absurd ((mkI_some_mem_copy hx).1 h).1 (Bool.self_ne_not γ)
        · rw [← Bool.not_not γ]; exact mem_over.1 h
      exact hc γ ((mkI_some_mem_copy hx).2 ⟨rfl, h⟩)

end Globular

section Molecule

variable {V : LowerSet U}

theorem isMoleculeIn_copy (hV : IsMoleculeIn U V) (α : Bool) :
    IsMoleculeIn (partialCylinder U K) (copy K α V) := by
  classical
  rw [← map_partialCylinderEndpoint]
  exact isMoleculeIn_map (partialCylinderEndpoint U K α) hV

theorem isSubmoleculeOf_copy {W : LowerSet U} (h : U.IsSubmoleculeOf V W) (α : Bool) :
    (partialCylinder U K).IsSubmoleculeOf (copy K α V) (copy K α W) := by
  classical
  rw [← map_partialCylinderEndpoint, ← map_partialCylinderEndpoint]
  exact (isSubmoleculeOf_map_iff (partialCylinderEndpoint U K α)).2 h

variable (K) in
def CylinderStatement (V : LowerSet U) : Prop :=
  IsMoleculeIn (partialCylinder U K) (over K V) ∧
    ∀ (d : ℕ), krullDim V = d → ∀ α : Bool,
      (partialCylinder U K).IsSubmoleculeOf (copy K α V)
        ((partialCylinder U K).boundary (over K V) d α) ∧
      (0 < d → (partialCylinder U K).IsSubmoleculeOf
        (over K (U.boundary V (d - 1) (!α)))
        ((partialCylinder U K).boundary (over K V) d α))

variable (K) in
def CylinderBelow (V : LowerSet U) : Prop :=
  ∀ W : LowerSet U, (W : Set U).ncard < (V : Set U).ncard →
    IsMoleculeIn U W → CylinderStatement K W

theorem isSubmoleculeOf_copy_boundary {W : LowerSet U} (hW : IsMoleculeIn U W) {n : ℕ}
    (hn : (n : WithBot ℕ∞) ≤ krullDim W) (α : Bool) (S : CylinderStatement K (U.boundary W n α)) :
    (partialCylinder U K).IsSubmoleculeOf (copy K α (U.boundary W n α))
      ((partialCylinder U K).boundary (over K W) n α) := by
  rw [boundary_over_boundary hW.isGlobular]
  exact (S.2 n (hW.krullDim_boundary hn α) α).1

theorem isSubmoleculeOf_copy_boundary_of_lt (hV : IsMoleculeIn U V) (IH : CylinderBelow K V)
    {n : ℕ} (hn : (n : WithBot ℕ∞) < krullDim V) (γ : Bool) :
    (partialCylinder U K).IsSubmoleculeOf (copy K γ (U.boundary V n γ))
      ((partialCylinder U K).boundary (over K V) n γ) :=
  isSubmoleculeOf_copy_boundary hV hn.le γ
    (IH _ (Set.ncard_lt_ncard (boundary_lt_iff.2 hn) hV.finite) (hV.boundary n γ))

theorem boundary_over_top (hV : IsMoleculeIn U V) (IH : CylinderBelow K V) {e : ℕ}
    (he : krullDim V = ((e + 1 : ℕ) : WithBot ℕ∞)) (α : Bool) :
    IsMoleculeIn (partialCylinder U K)
        ((partialCylinder U K).boundary (over K V) (e + 1) α) ∧
      (partialCylinder U K).IsSubmoleculeOf (copy K α V)
        ((partialCylinder U K).boundary (over K V) (e + 1) α) ∧
      (partialCylinder U K).IsSubmoleculeOf (over K (U.boundary V e (!α)))
        ((partialCylinder U K).boundary (over K V) (e + 1) α) := by
  have gV := hV.isGlobular
  have gX := isGlobular_over (K := K) gV
  have heV : (e : WithBot ℕ∞) < krullDim V := by rw [he]; exact_mod_cast Nat.lt_succ_self e
  set V' := U.boundary V e (!α)
  have mV' : IsMoleculeIn U V' := hV.boundary e (!α)
  have SV' := IH V' (Set.ncard_lt_ncard (boundary_lt_iff.2 heV) hV.finite) mV'
  have dV' : krullDim V' = e := hV.krullDim_boundary heV.le (!α)
  have hV'V : V' ≤ V := boundary_le V e _
  have hZ (γ : Bool) :
      (partialCylinder U K).boundary
        ((partialCylinder U K).boundary (over K V) (e + 1) α) e γ =
      (partialCylinder U K).boundary (over K V) e γ :=
    gX e (e + 1) (Nat.lt_succ_self e) γ α
  have hZ' : (partialCylinder U K).boundary (over K V) e (!α) =
      (partialCylinder U K).boundary (over K V') e (!α) :=
    boundary_over_boundary gV e (!α)
  refine isMoleculeIn_and_isSubmoleculeOf_of_genPasting (k := e) α ?_ (isMoleculeIn_copy hV α)
    SV'.1 ?_ ?_ ?_ ?_ ?_ ?_
  · rw [boundary_over_succ gV, boundary_eq_self he.le]
  · rw [copy_inf_over, inf_eq_right.2 hV'V, boundary_copy]
    exact .refl (isMoleculeIn_copy mV' α)
  · rw [copy_inf_over, inf_eq_right.2 hV'V]
    exact (SV'.2 e dV' α).1
  · rw [hZ, boundary_copy]
    exact isSubmoleculeOf_copy_boundary_of_lt hV IH heV α
  · rw [hZ, hZ']
    exact .refl (SV'.1.boundary e _)
  · rw [hZ, boundary_copy]
    rintro z ⟨hzA, hzB⟩
    rcases mem_copy_or_mem_over_of_mem_boundary_over hzB with h | ⟨he0, h⟩
    · exact h
    · have h' : z ∈ copy K α (V ⊓ U.boundary V (e - 1) (!α)) := by
        rw [← copy_inf_over]; exact ⟨hzA, h⟩
      exact copy_mono α (inf_le_right.trans (gV.boundary_le_boundary (by omega) _ _)) h'
  · rw [hZ, hZ']
    exact inf_le_right

theorem isMoleculeIn_over_Iic {t : U} (ht : t ∉ K) (hr : U.IsRound (.Iic t))
    (hZ : ∀ α, IsMoleculeIn (partialCylinder U K)
      ((partialCylinder U K).boundary (over K (.Iic t)) (grade ℕ t) α)) :
    IsMoleculeIn (partialCylinder U K) (over K (.Iic t)) := by
  have hKV : K ⊓ .Iic t ≤ U.bdryFull (.Iic t) := fun y ⟨hyK, hyt⟩ => by
    change y ∈ ((U.bdry (.Iic t) false ⊔ U.bdry (.Iic t) true : LowerSet U) : Set U)
    rw [coe_bdry_Iic_sup]
    exact lt_of_le_of_ne hyt fun h => ht (h ▸ hyK)
  have rX : (partialCylinder U K).IsRound (over K (.Iic t)) := isRound_over hr hKV
  have hd : krullDim (LowerSet.Iic (mkI K none t ht)) = ((grade ℕ t + 1 : ℕ) : WithBot ℕ∞) := by
    rw [LowerSet.krullDim_Iic, grade_mkI_none]
  rw [← Iic_mkI_none ht] at rX hZ ⊢
  refine .atom (mkI K none t ht) rX fun α => ?_
  rw [bdry_eq_boundary hd]
  exact hZ α

theorem isSubmoleculeOf_over_boundary {W : LowerSet U} (hW : IsMoleculeIn U W) {n : ℕ}
    (hn : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ krullDim W) (α : Bool)
    (S : CylinderStatement K (U.boundary W (n + 1) α)) :
    (partialCylinder U K).IsSubmoleculeOf (over K (U.boundary W n (!α)))
      ((partialCylinder U K).boundary (over K W) (n + 1) α) := by
  have t := (S.2 (n + 1) (hW.krullDim_boundary hn α) α).2 (Nat.succ_pos n)
  rw [Nat.add_sub_cancel, hW.isGlobular n (n + 1) (Nat.lt_succ_self n) (!α) α,
    ← boundary_over_boundary hW.isGlobular] at t
  exact t

theorem isSubmoleculeOf_boundary_over_of_isPastingIn {k : ℕ} (α : Bool) {F G : LowerSet U}
    (hF : IsMoleculeIn U F) (hG : IsMoleculeIn U G)
    (hp : U.IsPastingIn k (cond α G F) (cond α F G) V) (hV : IsMoleculeIn U V) (sG : G < V)
    (hk : (k : WithBot ℕ∞) < krullDim G) (IH : CylinderBelow K V) :
    (partialCylinder U K).IsSubmoleculeOf
      ((partialCylinder U K).boundary (over K G) (k + 1) α)
      ((partialCylinder U K).boundary (over K V) (k + 1) α) := by
  have hkG : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ krullDim G := by
    obtain ⟨d, hd⟩ := hG.exists_krullDim_eq
    rw [hd] at hk ⊢
    exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast hk)
  have hkV : (k : WithBot ℕ∞) < krullDim V := hk.trans_le (LowerSet.krullDim_mono sG.le)
  have gV := hV.isGlobular
  have gF := hF.isGlobular
  have gG := hG.isGlobular
  have gX := isGlobular_over (K := K) gV
  have gY := isGlobular_over (K := K) gG
  have hq := (isPastingIn_cond_comm α).1 hp
  obtain ⟨-, hint1, hint2⟩ := (isPastingIn_cond_iff α).1 hp
  have hmeet : U.boundary F k (!α) = U.boundary G k α := hint1.symm.trans hint2
  have hVα : U.boundary V k α = U.boundary F k α := hp.boundary_cond α
  have hVnα : U.boundary V k (!α) = U.boundary G k (!α) := hq.boundary_cond (!α)
  have hV1 : U.boundary V (k + 1) α = U.boundary F (k + 1) α ⊔ U.boundary G (k + 1) α :=
    hq.boundary_eq_sup_of_lt_cond (!α) gF gG (Nat.lt_succ_self k) α
  have IHG : ∀ X ≤ G, IsMoleculeIn U X → CylinderStatement K X := fun X hX hmX =>
    IH X (Set.ncard_lt_ncard (lt_of_le_of_lt hX sG) hV.finite) hmX
  have SG := IHG G le_rfl hG
  have hZk (γ : Bool) :
      (partialCylinder U K).boundary
        ((partialCylinder U K).boundary (over K V) (k + 1) α) k γ =
      (partialCylinder U K).boundary (over K V) k γ :=
    gX k (k + 1) (Nat.lt_succ_self k) γ α
  have hYk (γ : Bool) :
      (partialCylinder U K).boundary
        ((partialCylinder U K).boundary (over K G) (k + 1) α) k γ =
      (partialCylinder U K).boundary (over K G) k γ :=
    gY k (k + 1) (Nat.lt_succ_self k) γ α
  have hXG : (partialCylinder U K).boundary (over K V) k (!α) =
      (partialCylinder U K).boundary (over K G) k (!α) := by
    rw [boundary_over_boundary gV, hVnα, ← boundary_over_boundary gG]
  have hA : copy K α (U.boundary F (k + 1) α) ⊓
      (partialCylinder U K).boundary (over K G) (k + 1) α =
      copy K α (U.boundary F k (!α)) := by
    rw [boundary_over_succ gG, inf_sup_left, copy_inf_over, ← copy_inf, ← copy_sup]
    congr 1
    refine le_antisymm (sup_le ?_ ?_) ?_
    · rw [← hint1, inf_comm G]
      exact inf_le_inf (boundary_le F _ _) (boundary_le G _ _)
    · rw [← hint1, inf_comm G]
      exact inf_le_inf (boundary_le F _ _) (boundary_le G _ _)
    · refine le_sup_of_le_left (le_inf (gF.boundary_le_boundary (Nat.lt_succ_self k) _ _) ?_)
      rw [hmeet]
      exact gG.boundary_le_boundary (Nat.lt_succ_self k) _ _
  refine (isMoleculeIn_and_isSubmoleculeOf_of_genPasting (k := k) α ?_
    (isMoleculeIn_copy (hF.boundary (k + 1) α) α)
    (SG.1.boundary (k + 1) α) ?_ ?_ ?_ ?_ ?_ ?_).2.2
  · rw [boundary_over_succ gV, boundary_over_succ gG, hV1, copy_sup, hVnα, sup_assoc]
  · rw [hA, boundary_copy, gF k (k + 1) (Nat.lt_succ_self k)]
    exact .refl (isMoleculeIn_copy (hF.boundary k (!α)) α)
  · rw [hA, hYk, hmeet]
    exact isSubmoleculeOf_copy_boundary hG (le_trans (by exact_mod_cast Nat.le_succ k) hkG) α
      (IHG _ (boundary_le G _ _) (hG.boundary k α))
  · rw [hZk, boundary_copy, gF k (k + 1) (Nat.lt_succ_self k), ← hVα]
    exact isSubmoleculeOf_copy_boundary_of_lt hV IH hkV α
  · rw [hZk, hYk, hXG]
    exact .refl (SG.1.boundary k (!α))
  · classical
    rw [hZk, boundary_copy, gF k (k + 1) (Nat.lt_succ_self k)]
    rintro z ⟨hzA, hzB⟩
    have hE := (mem_copy.1 hzA).2
    rcases mem_copy_or_mem_over_of_mem_boundary_over hzB with h | ⟨hk0, h⟩
    · rwa [hVα] at h
    · refine mem_copy.2 ⟨?_, hE⟩
      have h' := mem_over.1 h
      rw [hp.boundary_eq_of_lt_cond α gG gF (by omega) (!α)] at h'
      exact gF.boundary_le_boundary (by omega) _ _ h'
  · rw [hZk, hYk, hXG]
    exact inf_le_right

private theorem inf_boundary_over_le_cond {k : ℕ} (β : Bool) {A B : LowerSet U}
    (gA : U.IsGlobular A) (gB : U.IsGlobular B) (gV : U.IsGlobular V)
    (hp : U.IsPastingIn k (cond β A B) (cond β B A) V) :
    over K B ⊓ (partialCylinder U K).boundary (over K V) (k + 1) (!β) ≤
      (partialCylinder U K).boundary (over K B) (k + 1) (!β) := by
  classical
  rw [boundary_over_succ gV, boundary_over_succ gB,
    hp.boundary_eq_sup_of_lt_cond β gA gB (Nat.lt_succ_self k), Bool.not_not, hp.boundary_cond β]
  rintro z ⟨hzB, hz⟩
  rcases hz with h | h
  · refine Or.inl (mem_copy.2 ⟨?_, (mem_copy.1 h).2⟩)
    rcases (mem_copy.1 h).1 with h' | h'
    · have hw : partialCylinderProj U K z ∈ A ⊓ B := ⟨boundary_le A _ _ h', mem_over.1 hzB⟩
      rw [((isPastingIn_cond_iff β).1 hp).2.1] at hw
      exact gB.boundary_le_boundary (Nat.lt_succ_self k) _ _ hw
    · exact h'
  · exact Or.inr h

theorem genPastingConditions_over_of_isPastingIn {k : ℕ} {W W' : LowerSet U}
    (hp : U.IsPastingIn k W W' V) (hV : IsMoleculeIn U V) (hW : IsMoleculeIn U W)
    (hW' : IsMoleculeIn U W') (sW : W < V) (sW' : W' < V)
    (hk : (k : WithBot ℕ∞) < min (krullDim W) (krullDim W')) (IH : CylinderBelow K V) :
    (partialCylinder U K).IsSubmoleculeOf (over K W' ⊓ over K W)
        ((partialCylinder U K).boundary (over K W') (k + 1) true) ∧
      (partialCylinder U K).IsSubmoleculeOf (over K W' ⊓ over K W)
        ((partialCylinder U K).boundary (over K W) (k + 1) false) ∧
      (partialCylinder U K).IsSubmoleculeOf
        ((partialCylinder U K).boundary (over K W') (k + 1) false)
        ((partialCylinder U K).boundary (over K V) (k + 1) false) ∧
      (partialCylinder U K).IsSubmoleculeOf
        ((partialCylinder U K).boundary (over K W) (k + 1) true)
        ((partialCylinder U K).boundary (over K V) (k + 1) true) ∧
      over K W' ⊓ (partialCylinder U K).boundary (over K V) (k + 1) false ≤
        (partialCylinder U K).boundary (over K W') (k + 1) false ∧
      over K W ⊓ (partialCylinder U K).boundary (over K V) (k + 1) true ≤
        (partialCylinder U K).boundary (over K W) (k + 1) true := by
  have gV := hV.isGlobular
  have gW := hW.isGlobular
  have gW' := hW'.isGlobular
  have hc {B : LowerSet U} (hB : IsMoleculeIn U B) (sB : B < V)
      (hkB : (k : WithBot ℕ∞) < krullDim B) (β : Bool) (hint : W ⊓ W' = U.boundary B k (!β)) :
      (partialCylinder U K).IsSubmoleculeOf (over K W' ⊓ over K W)
        ((partialCylinder U K).boundary (over K B) (k + 1) β) := by
    obtain ⟨d, hd⟩ := hB.exists_krullDim_eq
    rw [← over_inf, inf_comm, hint]
    rw [hd] at hkB
    refine isSubmoleculeOf_over_boundary hB ?_ β (IH _ (Set.ncard_lt_ncard
      (lt_of_le_of_lt (boundary_le B _ _) sB) hV.finite) (hB.boundary _ _))
    rw [hd]
    exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast hkB)
  exact ⟨hc hW' sW' (lt_min_iff.1 hk).2 true hp.inf_eq_input,
    hc hW sW (lt_min_iff.1 hk).1 false hp.inf_eq_output,
    isSubmoleculeOf_boundary_over_of_isPastingIn false hW hW' hp hV sW' (lt_min_iff.1 hk).2 IH,
    isSubmoleculeOf_boundary_over_of_isPastingIn true hW' hW hp hV sW (lt_min_iff.1 hk).1 IH,
    inf_boundary_over_le_cond true gW gW' gV hp, inf_boundary_over_le_cond false gW' gW gV hp⟩

theorem isMoleculeIn_over_of_isPastingIn {k : ℕ} {W W' : LowerSet U}
    (hp : U.IsPastingIn k W W' V) (hV : IsMoleculeIn U V) (hW : IsMoleculeIn U W)
    (hW' : IsMoleculeIn U W') (sW : W < V) (sW' : W' < V)
    (hk : (k : WithBot ℕ∞) < min (krullDim W) (krullDim W')) (IH : CylinderBelow K V) :
    IsMoleculeIn (partialCylinder U K) (over K V) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    genPastingConditions_over_of_isPastingIn hp hV hW hW' sW sW' hk IH
  have mW := (IH W (Set.ncard_lt_ncard sW hV.finite) hW).1
  have mW' := (IH W' (Set.ncard_lt_ncard sW' hV.finite) hW').1
  refine (isMoleculeIn_and_isSubmoleculeOf_of_genPasting (k := k + 1) false ?_ mW' mW
    h1 h2 h3 h4 h5 h6).1
  rw [← hp.sup_eq, over_sup, sup_comm]

theorem cylinderStatement_of_isMoleculeIn :
    ∀ s : ℕ, ∀ V : LowerSet U, (V : Set U).ncard = s → IsMoleculeIn U V →
      CylinderStatement K V := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro V hs hV
    have IH : CylinderBelow K V := fun W hW hmW => ih _ (hs ▸ hW) W rfl hmW
    have htop (d : ℕ) (hd : krullDim V = d) (α : Bool) :
        IsMoleculeIn (partialCylinder U K)
          ((partialCylinder U K).boundary (over K V) d α) ∧
        (partialCylinder U K).IsSubmoleculeOf (copy K α V)
          ((partialCylinder U K).boundary (over K V) d α) ∧
        (0 < d → (partialCylinder U K).IsSubmoleculeOf
          (over K (U.boundary V (d - 1) (!α)))
          ((partialCylinder U K).boundary (over K V) d α)) := by
      rcases Nat.eq_zero_or_pos d with rfl | hpos
      · rw [boundary_over_zero, boundary_eq_self hd.le]
        exact ⟨isMoleculeIn_copy hV α, .refl (isMoleculeIn_copy hV α),
          fun h => absurd h (lt_irrefl 0)⟩
      · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
        have t := boundary_over_top hV IH hd α
        rw [Nat.add_sub_cancel]
        exact ⟨t.1, t.2.1, fun _ => t.2.2⟩
    refine ⟨?_, fun d hd α => ⟨(htop d hd α).2.1, (htop d hd α).2.2⟩⟩
    have hV0 := hV
    cases hV0 with
    | point x hx =>
      by_cases hxK : x ∈ K
      · rw [over_eq_copy_of_le (LowerSet.Iic_le.2 hxK) false]
        exact isMoleculeIn_copy hV false
      · have hd : krullDim (LowerSet.Iic x) = ((grade ℕ x : ℕ) : WithBot ℕ∞) :=
          LowerSet.krullDim_Iic x
        have hr : U.IsRound (.Iic x) := by
          have h0 : grade ℕ x = 0 := isMin_iff_eq_bot.1 (hx.grade ℕ)
          have hself (n : ℕ) (γ : Bool) : U.boundary (.Iic x) n γ = .Iic x :=
            boundary_eq_self (by rw [hd, h0]; exact_mod_cast Nat.zero_le n) γ
          refine ⟨fun k n _ α β => by rw [hself, hself], fun h => ?_, fun n hn => ?_⟩
          · rw [hd, h0] at h; exact absurd h (lt_irrefl 0)
          · rw [hd, h0] at hn; exact absurd hn (not_lt.2 (by exact_mod_cast Nat.zero_le _))
        exact isMoleculeIn_over_Iic hxK hr fun α => (htop (grade ℕ x) hd α).1
    | atom t hr _ =>
      by_cases htK : t ∈ K
      · rw [over_eq_copy_of_le (LowerSet.Iic_le.2 htK) false]
        exact isMoleculeIn_copy hV false
      · exact isMoleculeIn_over_Iic htK hr
          fun α => (htop (grade ℕ t) (LowerSet.krullDim_Iic t) α).1
    | paste k W W' _ hp hW hW' hk =>
      have sW : W < V := hp.lt_cond false (hk.trans_le (min_le_right _ _))
      have sW' : W' < V := hp.lt_cond true (hk.trans_le (min_le_left _ _))
      exact isMoleculeIn_over_of_isPastingIn hp hV hW hW' sW sW' hk IH

end Molecule

theorem isMoleculeIn_over {V : LowerSet U} (hV : IsMoleculeIn U V) :
    IsMoleculeIn (partialCylinder U K) (over K V) :=
  (cylinderStatement_of_isMoleculeIn _ V rfl hV).1

end PartialCylinder

open PartialCylinder

theorem isMolecule_partialCylinder {U : OGP.{u}} (hU : IsMolecule U) (K : LowerSet U) :
    IsMolecule (partialCylinder U K) := by
  have h := isMoleculeIn_over (K := K) hU
  rwa [over_top] at h

theorem isRound_partialCylinder {U : OGP.{u}} (hr : U.IsRound ⊤) {K : LowerSet U}
    (hKU : K ≤ U.bdryFull ⊤) : (partialCylinder U K).IsRound ⊤ := by
  have h := isRound_over (K := K) hr (inf_le_left.trans hKU)
  rwa [over_top] at h

theorem krullDim_partialCylinder {U : OGP.{u}} {K : LowerSet U} {d : ℕ}
    (hd : krullDim U = d) (hKU : ∃ x, x ∉ K ∧ grade ℕ x = d) :
    krullDim (partialCylinder U K) = ((d + 1 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨x, hx, hdx⟩ := hKU
  have h1 := krullDim_over_le (K := K) (V := ⊤) (by rw [LowerSet.krullDim_top, hd])
  have h2 := grade_add_one_le_krullDim_over (K := K) (V := ⊤) trivial hx
  rw [over_top, LowerSet.krullDim_top] at h1 h2
  exact le_antisymm h1 (hdx ▸ h2)

theorem exists_notMem_bdryFull_grade_eq {U : OGP.{u}} (hU : IsMolecule U) {d : ℕ}
    (hd : krullDim U = d) : ∃ x, x ∉ U.bdryFull ⊤ ∧ grade ℕ x = d := by
  have hle (x : U) : grade ℕ x ≤ d := krullDim_le_coe_iff.1 hd.le x
  obtain ⟨x, hx⟩ : ∃ x : U, grade ℕ x = d := by
    rcases d with _ | m
    · obtain ⟨x, -⟩ := hU.nonempty
      exact ⟨x, Nat.eq_zero_of_le_zero (hle x)⟩
    · obtain ⟨x, hx⟩ := coe_lt_krullDim_iff.1
        (show (m : WithBot ℕ∞) < krullDim U by rw [hd]; exact_mod_cast Nat.lt_succ_self m)
      have hxm := hle x
      exact ⟨x, by omega⟩
  refine ⟨x, fun hmem => ?_, hx⟩
  rcases d with _ | m
  · rw [bdryFull, bdry_eq_bot (by rw [LowerSet.krullDim_top, hd]; rfl),
      bdry_eq_bot (by rw [LowerSet.krullDim_top, hd]; rfl), sup_bot_eq] at hmem
    exact hmem
  · have hd' : krullDim (⊤ : LowerSet U) = ((m + 1 : ℕ) : WithBot ℕ∞) := by
      rw [LowerSet.krullDim_top, hd]
    rw [bdryFull, bdry_eq_boundary hd', bdry_eq_boundary hd'] at hmem
    have hgm : grade ℕ x ≤ m := hmem.elim grade_le_of_mem_boundary grade_le_of_mem_boundary
    omega

theorem map_endpoint_eq_boundary_zero {U : OGP.{u}} [DecidablePred (· ∈ U.bdryFull ⊤)]
    (hd : krullDim U ≤ 0) (α : Bool) :
    map (partialCylinderEndpoint U (U.bdryFull ⊤) α) ⊤ =
      (partialCylinder U (U.bdryFull ⊤)).boundary ⊤ 0 α := by
  rw [map_partialCylinderEndpoint, ← over_top (K := U.bdryFull ⊤), boundary_over_zero,
    boundary_eq_self (by rwa [LowerSet.krullDim_top])]

section CylinderBoundary

variable {U : OGP.{u}} (K : LowerSet U) (hU : IsMolecule U) {e : ℕ}
  (he : krullDim U = ((e + 1 : ℕ) : WithBot ℕ∞))

include hU he

theorem boundary_partialCylinder_eq (β : Bool) :
    (partialCylinder U K).boundary ⊤ (e + 1) β =
      copy K β ⊤ ⊔ over K (U.boundary ⊤ e (!β)) := by
  rw [← over_top (K := K), boundary_over_succ hU.isGlobular e β,
    boundary_eq_self (by rw [LowerSet.krullDim_top, he])]

omit he in
theorem boundary_partialCylinder_dimension {d : ℕ} (hd : krullDim U = d) (hpos : 0 < d)
    (β : Bool) :
    (partialCylinder U K).boundary ⊤ d β =
      copy K β ⊤ ⊔ over K (U.boundary ⊤ (d - 1) (!β)) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact boundary_partialCylinder_eq K hU hd β

omit he in
theorem map_endpoint_eq_boundary_dimension [DecidablePred (· ∈ K)] {d : ℕ}
    (hd : krullDim U = d) (hpos : 0 < d) {β : Bool}
    (hsub : U.boundary ⊤ (d - 1) (!β) ≤ K) :
    map (partialCylinderEndpoint U K β) ⊤ =
      (partialCylinder U K).boundary ⊤ d β := by
  rw [map_partialCylinderEndpoint, boundary_partialCylinder_dimension K hU hd hpos,
    over_eq_copy_of_le hsub β, ← copy_sup, top_sup_eq]

end CylinderBoundary

end Atoms.Molecule.OGP
