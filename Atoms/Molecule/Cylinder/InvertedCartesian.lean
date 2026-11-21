import Atoms.Molecule.Cylinder.InvertedMolecule

universe u

open CategoryTheory Order Set Topology

namespace Atoms.Molecule.OGP

namespace InvertedCylinder

open PartialCylinder

variable {U : OGP.{u}} {K : LowerSet U} {ε : Bool} {x y : U}

abbrev ZigZag {P Q : OGP.{u}} (S : LowerSet P) (f : P → Q) (w : Q) (y z : P) : Prop :=
  Relation.ReflTransGen
    (fun a b => a ∈ (S : Set P) ∩ f ⁻¹' Ici w ∧ b ∈ (S : Set P) ∩ f ⁻¹' Ici w ∧ (a ≤ b ∨ b ≤ a))
    y z

theorem ZigZag.single {P Q : OGP.{u}} {S : LowerSet P} {f : P → Q} {w : Q} {a b : P}
    (ha : a ∈ S) (hb : b ∈ S) (hwa : w ≤ f a) (hwb : w ≤ f b) (hab : a ≤ b ∨ b ≤ a) :
    ZigZag S f w a b :=
  Relation.ReflTransGen.single ⟨⟨ha, hwa⟩, ⟨hb, hwb⟩, hab⟩

theorem ZigZag.symm {P Q : OGP.{u}} {S : LowerSet P} {f : P → Q} {w : Q} {a b : P}
    (h : ZigZag S f w a b) : ZigZag S f w b a :=
  haveI : Std.Symm (fun a b =>
      a ∈ (S : Set P) ∩ f ⁻¹' Ici w ∧ b ∈ (S : Set P) ∩ f ⁻¹' Ici w ∧ (a ≤ b ∨ b ≤ a)) :=
    ⟨fun _ _ ⟨h1, h2, h3⟩ => ⟨h2, h1, h3.symm⟩⟩
  Relation.ReflTransGen.stdSymm.symm a b h

theorem ZigZag.map {P P' Q : OGP.{u}} {S : LowerSet P} {T : LowerSet P'} {φ : P → Q} {φ' : P' → Q}
    {w : Q} (g : P → P') (hgS : ∀ c ∈ S, g c ∈ T) (hgle : ∀ c d, c ≤ d → g c ≤ g d)
    (hgφ : ∀ c ∈ S, w ≤ φ c → w ≤ φ' (g c)) {a b : P} (h : ZigZag S φ w a b) :
    ZigZag T φ' w (g a) (g b) :=
  Relation.ReflTransGen.lift g
    (fun c d ⟨⟨hcS, hwc⟩, ⟨hdS, hwd⟩, hcd⟩ =>
      ⟨⟨hgS c hcS, hgφ c hcS hwc⟩, ⟨hgS d hdS, hgφ d hdS hwd⟩,
        hcd.imp (hgle c d) (hgle d c)⟩) a b h

theorem zigZag_of_isMap {P Q : OGP.{u}} {p : P → Q} (hp : IsMap p) (x : P) (n : ℕ) (α : Bool)
    {b b' : P} (hb : b ∈ P.boundary (.Iic x) n α) (hb' : b' ∈ P.boundary (.Iic x) n α)
    (h : p b = p b') : ZigZag (P.boundary (.Iic x) n α) p (p b) b b' :=
  IsUpperSet.isPreconnected_iff_reflTransGen.1
    ((hp.finalOn x n α).2 (p b) ((hp.finalOn x n α).1 hb)).2 b ⟨hb, le_rfl⟩ b' ⟨hb', h.le⟩

theorem zigZag_Iic_of_isMap {P Q : OGP.{u}} {p : P → Q} (hp : IsMap p) {x b b' : P}
    (hb : b ∈ LowerSet.Iic x) (hb' : b' ∈ LowerSet.Iic x) (h : p b = p b') :
    ZigZag (.Iic x) p (p b) b b' := by
  have hself : P.boundary (.Iic x) (grade ℕ x) true = .Iic x :=
    boundary_eq_self (LowerSet.krullDim_Iic x).le true
  simpa only [hself] using
    zigZag_of_isMap hp x (grade ℕ x) true (hself.symm ▸ hb) (hself.symm ▸ hb') h

theorem zigZag_of_lift {W : OGP.{u}} [DecidablePred (· ∈ K)] {n : ℕ} {p : U → W} {B : LowerSet U}
    {S : LowerSet (invertedCylinder U K ε n)} (β : Bool)
    (h1 : ∀ y ∈ S, partialCylinderProj U K y ∈ B)
    (h2 : ∀ c ∈ B, partialCylinderEndpoint U K β c ∈ S)
    (h3 : ∀ y ∈ S, ZigZag S (fun a => p (partialCylinderProj U K a))
      (p (partialCylinderProj U K y)) y
      (partialCylinderEndpoint U K β (partialCylinderProj U K y)))
    (h4 : ∀ b ∈ B, ∀ b' ∈ B, p b = p b' → ZigZag B p (p b) b b') :
    ∀ y ∈ S, ∀ z ∈ S, p (partialCylinderProj U K y) = p (partialCylinderProj U K z) →
      ZigZag S (fun a => p (partialCylinderProj U K a)) (p (partialCylinderProj U K y))
        y z := by
  intro y hy z hz hyz
  have hb := ZigZag.map (P' := invertedCylinder U K ε n) (φ := p)
    (φ' := fun a => p (partialCylinderProj U K a)) (partialCylinderEndpoint U K β) h2
    (fun _ _ h => (IsInclusion.le_iff (partialCylinderEndpoint U K β)).2 h)
    (fun _ _ h => by simpa only [partialCylinderProj_endpoint] using h)
    (h4 _ (h1 y hy) _ (h1 z hz) hyz)
  have hz' := (h3 z hz).symm
  rw [← hyz] at hz'
  exact ((h3 y hy).trans hb).trans hz'

theorem zigZag_endpoint_of_mkI_none_mem {W : OGP.{u}} [DecidablePred (· ∈ K)] {n : ℕ} {p : U → W}
    {S : LowerSet (invertedCylinder U K ε n)} (β : Bool)
    {y : invertedCylinder U K ε n} (hy : y ∈ S)
    (hb : partialCylinderEndpoint U K β (partialCylinderProj U K y) ∈ S)
    (hm : ∀ hK' : partialCylinderProj U K y ∉ K,
      mkI K none (partialCylinderProj U K y) hK' ∈ S) :
    ZigZag S (fun a => p (partialCylinderProj U K a)) (p (partialCylinderProj U K y)) y
      (partialCylinderEndpoint U K β (partialCylinderProj U K y)) := by
  by_cases hK' : partialCylinderProj U K y ∈ K
  · rw [← eq_endpoint_of_proj_mem y hK' β]
  · have hle1 : y ≤ mkI K none _ hK' := le_mkI_none_of_proj_le hK' le_rfl
    have hle2 : partialCylinderEndpoint U K β (partialCylinderProj U K y) ≤
        mkI K none _ hK' := endpoint_le_mkI_none β hK' le_rfl
    refine (ZigZag.single hy (hm hK') le_rfl le_rfl (Or.inl hle1)).trans
      (ZigZag.single (hm hK') hb le_rfl ?_ (Or.inr hle2))
    rw [partialCylinderProj_endpoint]

theorem zigZag_front {W : OGP.{u}} [DecidablePred (· ∈ K)] {p : U → W} (hpmap : IsMap p) {e : ℕ}
    (hdpx : grade ℕ (p x) ≤ e) {y : invertedCylinder U K ε (e + 1)}
    (hy : y ∈ copy K ε (.Iic x)) :
    ZigZag (P := invertedCylinder U K ε (e + 1))
      (copy K (!ε) (.Iic x) ⊔ over K (U.boundary (.Iic x) e ε) ⊔ copy K ε (.Iic x))
      (fun a => p (partialCylinderProj U K a))
      (p (partialCylinderProj U K y)) y
      (partialCylinderEndpoint U K (!ε) (partialCylinderProj U K y)) := by
  set X : LowerSet U := .Iic x with hXdef
  set F : LowerSet (invertedCylinder U K ε (e + 1)) :=
    copy K (!ε) X ⊔ over K (U.boundary X e ε) ⊔ copy K ε X with hFdef
  have hc1 (z : U) (hz : z ∈ X) : partialCylinderEndpoint U K (!ε) z ∈ F :=
    Or.inl (Or.inl (by rw [← map_partialCylinderEndpoint]; exact ⟨z, hz, rfl⟩))
  have hc2 (z : U) (hz : z ∈ X) : partialCylinderEndpoint U K ε z ∈ F :=
    Or.inr (by rw [← map_partialCylinderEndpoint]; exact ⟨z, hz, rfl⟩)
  have hfe (β : Bool) (z : U) :
      p (partialCylinderProj U K (partialCylinderEndpoint U K β z)) = p z := by
    rw [partialCylinderProj_endpoint]
  have hmono (β : Bool) {z z' : U} (h : z ≤ z') :
      partialCylinderEndpoint U K β z ≤ partialCylinderEndpoint U K β z' :=
    (IsInclusion.le_iff (partialCylinderEndpoint U K β)).2 h
  obtain ⟨hbX, hye⟩ := mem_copy.1 hy
  set b := partialCylinderProj U K y with hbdef
  by_cases hbK : b ∈ K
  · rw [← hye, endpoint_of_mem _ hbK, endpoint_of_mem _ hbK]
  have hxX : x ∈ X := LowerSet.mem_Iic_iff.2 le_rfl
  have hbx : b ≤ x := LowerSet.mem_Iic_iff.1 hbX
  have hpb : p b ≤ p x := hpmap.monotone hbx
  obtain ⟨c, hc, hcx⟩ : p x ∈ p '' (U.boundary X e ε : Set U) := by
    rw [hpmap.image_boundary x e ε,
      boundary_eq_self (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hdpx) ε]
    exact LowerSet.mem_Iic_iff.2 le_rfl
  have hcX : c ∈ X := boundary_le X e ε hc
  have hcx' : c ≤ x := LowerSet.mem_Iic_iff.1 hcX
  have hw (β : Bool) (z : U) (h : p z = p x) :
      p b ≤ p (partialCylinderProj U K (partialCylinderEndpoint U K β z)) := by
    rw [hfe, h]; exact hpb
  have s1 : ZigZag F (fun a => p (partialCylinderProj U K a)) (p b) y
      (partialCylinderEndpoint U K ε x) := by
    refine ZigZag.single (hye ▸ hc2 b hbX) (hc2 x hxX) le_rfl (hw ε x rfl) (Or.inl ?_)
    rw [← hye]; exact hmono ε hbx
  have s2 : ZigZag F (fun a => p (partialCylinderProj U K a)) (p b)
      (partialCylinderEndpoint U K ε x) (partialCylinderEndpoint U K ε c) :=
    ZigZag.single (hc2 x hxX) (hc2 c hcX) (hw ε x rfl) (hw ε c hcx) (Or.inr (hmono ε hcx'))
  have s3 : ZigZag F (fun a => p (partialCylinderProj U K a)) (p b)
      (partialCylinderEndpoint U K ε c) (partialCylinderEndpoint U K (!ε) c) := by
    by_cases hcK : c ∈ K
    · rw [endpoint_of_mem _ hcK, endpoint_of_mem _ hcK]
    · have hm : mkI K none c hcK ∈ F :=
        Or.inl (Or.inr ((mem_over (a := mkI K none c hcK)).2 hc))
      have hwm : p b ≤ p (partialCylinderProj U K (mkI K none c hcK)) := by
        change p b ≤ p c; rw [hcx]; exact hpb
      exact (ZigZag.single (hc2 c hcX) hm (hw ε c hcx) hwm
        (Or.inl (endpoint_le_mkI_none ε hcK le_rfl))).trans
        (ZigZag.single hm (hc1 c hcX) hwm (hw (!ε) c hcx)
          (Or.inr (endpoint_le_mkI_none (!ε) hcK le_rfl)))
  have s4 : ZigZag F (fun a => p (partialCylinderProj U K a)) (p b)
      (partialCylinderEndpoint U K (!ε) c) (partialCylinderEndpoint U K (!ε) x) :=
    ZigZag.single (hc1 c hcX) (hc1 x hxX) (hw _ c hcx) (hw _ x rfl) (Or.inl (hmono (!ε) hcx'))
  have s5 : ZigZag F (fun a => p (partialCylinderProj U K a)) (p b)
      (partialCylinderEndpoint U K (!ε) x) (partialCylinderEndpoint U K (!ε) b) :=
    ZigZag.single (hc1 x hxX) (hc1 b hbX) (hw _ x rfl) (by rw [hfe]) (Or.inr (hmono (!ε) hbx))
  exact (((s1.trans s2).trans s3).trans s4).trans s5

theorem finalOn_endpoint_top {W : OGP.{u}} {p : U → W} (hpmap : IsMap p)
    {e : ℕ} (hKd : ∀ z ∈ K, grade ℕ z < e + 1)
    (hdpx : grade ℕ (p x) ≤ e) (hx : x ∉ K) (m : ℕ) (α : Bool) :
    FinalOn (fun a => p (partialCylinderProj U K a))
      ((invertedCylinder U K ε (e + 1)).boundary (.Iic (mkI K (some ε) x hx)) m α)
      (W.boundary (.Iic (p x)) m α) := by
  classical
  set α' := xor (topDim (e + 1) (m + 1)) α with hα'
  have hS : (invertedCylinder U K ε (e + 1)).boundary (.Iic (mkI K (some ε) x hx)) m α =
      copy K ε (U.boundary (.Iic x) m α') := by
    have hcl : (LowerSet.Iic (mkI K (some ε) x hx) : LowerSet (invertedCylinder U K ε (e + 1))) =
        copy K ε (.Iic x) := by
      rw [← endpoint_of_notMem ε hx]; exact Iic_endpoint ε x
    rw [hcl, ← map_endpointDual hKd, ← map_boundary (endpointDual U K ε hKd),
      boundary_dual, map_endpointDual hKd]
  have hbd (γ : Bool) : W.boundary (.Iic (p x)) e γ = .Iic (p x) :=
    boundary_eq_self (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hdpx) γ
  rw [hS]
  refine finalOn_of_fibration (P := invertedCylinder U K ε (e + 1))
    (hpmap.isClosedMap.comp (isClosedMap_partialCylinderProj U K)) ?_ fun y hy z hz h => ?_
  · change (fun a => p (partialCylinderProj U K a)) '' _ = _
    rw [image_copy_comp, hpmap.image_boundary x m α']
    by_cases ht : topDim (e + 1) (m + 1) = true
    · have hm : m = e := by simp [topDim] at ht; omega
      subst hm
      rw [hbd, hbd]
    · have : α' = α := by rw [hα', Bool.eq_false_iff.2 ht, Bool.false_xor]
      rw [this]
  · obtain ⟨hyB, hye⟩ := mem_copy.1 hy
    obtain ⟨hzB, hze⟩ := mem_copy.1 hz
    have hz' := ZigZag.map (P' := invertedCylinder U K ε (e + 1)) (φ := p)
      (φ' := fun a => p (partialCylinderProj U K a))
      (S := U.boundary (.Iic x) m α')
      (T := copy K ε (U.boundary (.Iic x) m α')) (partialCylinderEndpoint U K ε)
      (fun c hc => by rw [← map_partialCylinderEndpoint]; exact ⟨c, hc, rfl⟩)
      (fun _ _ h => (IsInclusion.le_iff (partialCylinderEndpoint U K ε)).2 h)
      (fun _ _ h => by simpa only [partialCylinderProj_endpoint] using h)
      (zigZag_of_isMap hpmap x m α' hyB hzB h)
    rwa [hye, hze] at hz'

theorem finalOn_over {W : OGP.{u}} {n : ℕ} {p : U → W} (hpmap : IsMap p) {B : LowerSet U}
    {T : Set W} (hBT : p '' (B : Set U) = T)
    (hfin : ∀ b ∈ B, ∀ b' ∈ B, p b = p b' → ZigZag B p (p b) b b') :
    FinalOn (α := invertedCylinder U K ε n) (fun a => p (partialCylinderProj U K a))
      (over K B) T := by
  classical
  refine finalOn_of_fibration (P := invertedCylinder U K ε n)
    (hpmap.isClosedMap.comp (isClosedMap_partialCylinderProj U K))
    ((image_over_comp p B).trans hBT)
    (zigZag_of_lift true (fun y hy => mem_over.1 hy)
      (fun c hc => copy_le_over true B (by rw [← map_partialCylinderEndpoint]; exact ⟨c, hc, rfl⟩))
      (fun y hy => ?_) hfin)
  exact zigZag_endpoint_of_mkI_none_mem true hy
    ((mem_over (a := partialCylinderEndpoint U K true _)).2
      (by rw [partialCylinderProj_endpoint]; exact mem_over.1 hy))
    (fun hK' => (mem_over (a := mkI K none _ hK')).2 ((mem_over (a := y)).1 hy))

theorem finalOn_boundary_over {W : OGP.{u}} {n : ℕ} {p : U → W} (hpmap : IsMap p)
    {B : LowerSet U} {T : Set W} (gB : U.IsGlobular B) {m : ℕ}
    {α : Bool} (hself : U.boundary B m α = B) (hBT : p '' (B : Set U) = T)
    (hfin : ∀ b ∈ B, ∀ b' ∈ B, p b = p b' → ZigZag B p (p b) b b') :
    FinalOn (α := invertedCylinder U K ε n) (fun a => p (partialCylinderProj U K a))
      ((partialCylinder U K).boundary (over K B) m α) T := by
  classical
  have hsub : (partialCylinder U K).boundary (over K B) m α ≤ over K B :=
    boundary_le (P := partialCylinder U K) (over K B) m α
  have hcopy : copy K α B ≤ (partialCylinder U K).boundary (over K B) m α := by
    have h := copy_boundary_le_boundary_over (K := K) B m α
    rwa [hself] at h
  refine finalOn_of_fibration (P := invertedCylinder U K ε n)
    (hpmap.isClosedMap.comp (isClosedMap_partialCylinderProj U K)) ?_
    (zigZag_of_lift α (fun y hy => mem_over.1 (hsub hy))
      (fun c hc => hcopy (by rw [← map_partialCylinderEndpoint]; exact ⟨c, hc, rfl⟩))
      (fun y hy => ?_) hfin)
  · change (fun a => p (partialCylinderProj U K a)) '' _ = _
    rw [← hBT, ← image_over_comp (K := K) p B]
    refine Subset.antisymm (image_mono hsub) ?_
    rw [image_over_comp, ← image_copy_comp (K := K) p α B]
    exact image_mono hcopy
  · rcases mem_copy_or_mem_over_of_mem_boundary_over hy with h | ⟨hm, h⟩
    · rw [(mem_copy.1 h).2]
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hover := over_boundary_le_boundary_over (K := K) gB m' α
      rw [Nat.add_sub_cancel] at h
      refine zigZag_endpoint_of_mkI_none_mem α hy
        (hcopy (by
          rw [← map_partialCylinderEndpoint]
          exact ⟨_, mem_over.1 (hsub hy), rfl⟩))
        (fun hK' => hover ?_)
      exact (mem_over (a := mkI K none _ hK')).2 ((mem_over (a := y)).1 h)

theorem finalOn_front {W : OGP.{u}} {p : U → W} (hpmap : IsMap p) {e : ℕ}
    (hdpx : grade ℕ (p x) ≤ e) :
    FinalOn (α := invertedCylinder U K ε (e + 1)) (fun a => p (partialCylinderProj U K a))
      ((copy K (!ε) (.Iic x) ⊔ over K (U.boundary (.Iic x) e ε) ⊔ copy K ε (.Iic x) :
        LowerSet (invertedCylinder U K ε (e + 1))))
      (LowerSet.Iic (p x)) := by
  classical
  set X : LowerSet U := .Iic x with hXdef
  set F : LowerSet (invertedCylinder U K ε (e + 1)) :=
    copy K (!ε) X ⊔ over K (U.boundary X e ε) ⊔ copy K ε X with hFdef
  have hFX : F ≤ over K X :=
    sup_le (sup_le (copy_le_over _ _) (over_mono (boundary_le X _ _))) (copy_le_over _ _)
  have hcF : copy K (!ε) X ≤ F := le_sup_left.trans le_sup_left
  refine finalOn_of_fibration (P := invertedCylinder U K ε (e + 1))
    (hpmap.isClosedMap.comp (isClosedMap_partialCylinderProj U K)) ?_
    (zigZag_of_lift (!ε) (fun y hy => mem_over.1 (hFX hy))
      (fun c hc => hcF (by rw [← map_partialCylinderEndpoint]; exact ⟨c, hc, rfl⟩))
      (fun y hy => ?_) ?_)
  · change (fun a => p (partialCylinderProj U K a)) '' (F : Set (partialCylinder U K)) = Iic (p x)
    rw [← hpmap.image_Iic x, ← LowerSet.coe_Iic, ← hXdef, ← image_over_comp (K := K) p X]
    refine Subset.antisymm (image_mono hFX) ?_
    rw [image_over_comp, ← image_copy_comp (K := K) p (!ε) X]
    exact image_mono hcF
  · have hy' := hy
    rcases hy' with (h | h) | h
    · rw [(mem_copy.1 h).2]
    · exact zigZag_endpoint_of_mkI_none_mem (!ε) hy
        (hcF (by
          rw [← map_partialCylinderEndpoint]
          exact ⟨_, boundary_le X _ _ (mem_over.1 h), rfl⟩))
        (fun hK' =>
          Or.inl (Or.inr ((mem_over (a := mkI K none _ hK')).2 ((mem_over (a := y)).1 h))))
    · exact zigZag_front hpmap hdpx h
  · exact fun _ hb _ hb' h => zigZag_Iic_of_isMap hpmap hb hb' h

theorem finalOn_mkI_top (hU : IsMolecule U) {e : ℕ}
    (he : krullDim U = ((e + 1 : ℕ) : WithBot ℕ∞))
    (hKU : K ≤ U.boundary ⊤ e ε) {W : OGP.{u}} {p : U → W}
    (hpmap : IsMap p)
    (hPmap : IsMap (P := partialCylinder U K) (fun a => p (partialCylinderProj U K a)))
    (hdpx : grade ℕ (p x) ≤ e) (hx : x ∉ K) (hdx : grade ℕ x = e + 1) (m : ℕ) (α : Bool) :
    FinalOn (fun a => p (partialCylinderProj U K a))
      ((invertedCylinder U K ε (e + 1)).boundary (.Iic (mkI K none x hx)) m α)
      (W.boundary (.Iic (p x)) m α) := by
  have hUle (w : U) : grade ℕ w ≤ e + 1 := krullDim_le_coe_iff.1 he.le w
  have hKd := dim_lt_of_mem_K hKU
  have hKf := orient_eq_of_mem_K hKU
  set X : LowerSet U := .Iic x with hXdef
  have hXa : U.IsAtomIn X := hU.isAtomIn_Iic trivial
  have gX : U.IsGlobular X := hXa.isRound.isGlobular
  have hdX : krullDim X = ((e + 1 : ℕ) : WithBot ℕ∞) := by
    rw [hXdef, LowerSet.krullDim_Iic, hdx]
  set W' := U.boundary X e (!ε) with hW'def
  have gW' : U.IsGlobular W' := gX.boundary e (!ε)
  have hcl : (LowerSet.Iic (mkI K none x hx) : LowerSet (invertedCylinder U K ε (e + 1))) =
      over K X :=
    Iic_mkI_none hx
  have hbd (k : ℕ) (hk : e ≤ k) (γ : Bool) : W.boundary (.Iic (p x)) k γ = .Iic (p x) :=
    boundary_eq_self (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hdpx.trans hk) γ
  have hW'p : p '' (W' : Set U) = LowerSet.Iic (p x) := by
    rw [hpmap.image_boundary x e (!ε), hbd e le_rfl]
  have hW'fin : ∀ b ∈ W', ∀ b' ∈ W', p b = p b' → ZigZag W' p (p b) b b' :=
    fun _ hb _ hb' h => zigZag_of_isMap hpmap x e (!ε) hb hb' h
  have hXfin : ∀ b ∈ X, ∀ b' ∈ X, p b = p b' → ZigZag X p (p b) b b' :=
    fun _ hb _ hb' h => zigZag_Iic_of_isMap hpmap hb hb' h
  have hW'std : over K W' ≤ std K ε (e + 1) := fun z hz => mem_std_of_dim_lt (by
    have := grade_le_of_mem_boundary (mem_over.1 hz); omega)
  rcases Nat.lt_or_ge m e with hm | hm
  · rw [boundary_eq_of_add_two_le (by omega)]
    exact hPmap.finalOn (mkI K none x hx) m α
  rcases Nat.lt_or_ge m (e + 1) with hm' | hm'
  · obtain rfl : m = e := by omega
    have mX := isMoleculeIn_over_Iic_top (K := K) hU he hKU hx hdx
    rw [hcl, ← mX.isGlobular m (m + 1) (Nat.lt_succ_self m) α ε,
      boundary_over_top_eps hUle hKd hKf,
      boundary_eq_of_subset_std hW'std, hbd m le_rfl]
    exact finalOn_boundary_over (ε := ε) (n := m + 1) hpmap gW'
      (boundary_eq_self (krullDim_boundary_le X m (!ε)) α) hW'p hW'fin
  rcases Nat.lt_or_ge m (e + 2) with hm'' | hm''
  · obtain rfl : m = e + 1 := by omega
    rw [hcl, hbd _ (by omega)]
    rcases Bool.eq_or_eq_not α ε with rfl | rfl
    · rw [boundary_over_top_eps hUle hKd hKf]
      exact finalOn_over (ε := α) (n := e + 1) hpmap hW'p hW'fin
    · rw [boundary_over_top_not hUle hKd, sup_right_comm]
      exact finalOn_front hpmap hdpx
  · have hdS : krullDim (over K X) ≤ m :=
      (krullDim_over_top hKd hdX).le.trans (by exact_mod_cast hm'')
    rw [hcl, boundary_eq_self (P := invertedCylinder U K ε (e + 1)) hdS, hbd _ (by omega)]
    exact finalOn_over (ε := ε) (n := e + 1) hpmap (hpmap.image_Iic x) hXfin

theorem isMap_comp_invertedProj {U W : OGP.{u}} (hU : IsMolecule U) {n : ℕ}
    (hn : krullDim U = n) (hpos : 0 < n) {K : LowerSet U} {ε : Bool} (hKU : K ≤ U.bdry ⊤ ε)
    {p : U → W} (hp : IsMap p) (hd : krullDim W < n) :
    IsMap (P := invertedCylinder U K ε n) (fun a => p (partialCylinderProj U K a)) := by
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := ⟨n - 1, by omega⟩
  have hUle (w : U) : grade ℕ w ≤ e + 1 := krullDim_le_coe_iff.1 hn.le w
  have hdU : krullDim (⊤ : LowerSet U) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
    rw [LowerSet.krullDim_top, hn]
  have hKU' : K ≤ U.boundary ⊤ e ε := hKU.trans (bdry_eq_boundary hdU ε).le
  have hKd := dim_lt_of_mem_K hKU'
  have hPmap : IsMap (P := partialCylinder U K) (fun a => p (partialCylinderProj U K a)) :=
    (isMap_partialCylinderProj hU K).comp hp
  have hdp (x : U) : grade ℕ (p x) ≤ e := by
    have hlt : ((grade ℕ (p x) : ℕ) : WithBot ℕ∞) < ((e + 1 : ℕ) : WithBot ℕ∞) :=
      (grade_le_krullDim (p x)).trans_lt hd
    exact Nat.lt_succ_iff.1 (by exact_mod_cast hlt)
  refine ⟨hPmap.isClosedMap, fun a m α => ?_⟩
  cases hc : changed ε (e + 1) a
  · have hcl : LowerSet.Iic a ≤ std K ε (e + 1) :=
      LowerSet.Iic_le.2 (mem_std.2 hc)
    rw [boundary_eq_of_subset_std hcl]
    exact hPmap.finalOn a m α
  · rcases a with ⟨x, hx⟩ | ⟨⟨_ | β⟩, ⟨x, hx⟩⟩
    · simp [changed] at hc
    · have hdx : grade ℕ x = e + 1 := le_antisymm (hUle x) (of_decide_eq_true hc)
      exact finalOn_mkI_top hU hn hKU' hp hPmap (hdp x) hx hdx m α
    · obtain ⟨rfl, -⟩ : β = ε ∧ e + 1 ≤ grade ℕ x := of_decide_eq_true hc
      exact finalOn_endpoint_top hp hKd (hdp x) hx m α

theorem functor_isFibered_comp_invertedProj {U W : OGP.{u}} {K : LowerSet U} {ε : Bool} {n : ℕ}
    {p : U → W} (hp : Monotone p) [hp.functor.IsFibered]
    (hm : Monotone (fun a : invertedCylinder U K ε n => p (partialCylinderProj U K a))) :
    hm.functor.IsFibered :=
  Monotone.functor_isFibered_comp (monotone_partialCylinderProj U K) hp

end InvertedCylinder

end Atoms.Molecule.OGP
