import Atoms.Diagrammatic.GrayTensor.Context

open CategoryTheory Atoms.Molecule Atoms.Molecule.OGP Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

theorem PastingDiagram.Equiv.homAt {a b : PastingDiagram X} (e : a.Equiv b) (n : ℕ) :
    (a.homAt n).Equiv (b.homAt n) :=
  ⟨rfl, e.boundary n false, e.boundary n true⟩

theorem PastingDiagram.boundary_grayTensor_equiv_of_dim_eq_zero (z : PastingDiagram X)
    {v : PastingDiagram Y} (hv : v.dim = 0) (k : ℕ) (α : Bool) :
    ((z.boundary k α).grayTensor v).Equiv ((z.grayTensor v).boundary k α) := by
  have hv' (j : ℕ) (β : Bool) : v.shape.ogp.boundary ⊤ j β = ⊤ := by
    refine boundary_eq_self ?_ β
    rw [LowerSet.krullDim_top, v.shape.krullDim_eq_dimension]
    exact_mod_cast (hv.trans_le j.zero_le)
  refine (Equiv.grayTensor (.refl _) (equiv_boundary_dim v (hv.trans_le (k - k).zero_le)
    (xor k.bodd α)).symm).trans (Within.equiv_of_image_eq
      ((Within.boundaryGrayTensor z v le_rfl α).trans (Within.boundary _ k α))
      (Within.boundary _ k α) ?_)
  rw [Within.image_boundaryGrayTensor_trans, Within.image_boundary_grayTensor]
  refine congrArg _ (le_antisymm (le_iSup₂_of_le k le_rfl le_rfl) (iSup₂_le fun i hi => ?_))
  rw [hv', hv']
  exact LowerSet.prod_mono (by
    rcases hi.lt_or_eq with hi | rfl
    · exact z.shape.isMolecule.isGlobular.boundary_le_boundary hi α α
    · exact le_rfl) le_rfl

theorem PastingDiagram.grayTensor_boundary_equiv_of_dim_eq_zero {u : PastingDiagram X}
    (hu : u.dim = 0) (z : PastingDiagram Y) (k : ℕ) (α : Bool) :
    (u.grayTensor (z.boundary k α)).Equiv ((u.grayTensor z).boundary k α) := by
  have hu' (j : ℕ) (β : Bool) : u.shape.ogp.boundary ⊤ j β = ⊤ := by
    refine boundary_eq_self ?_ β
    rw [LowerSet.krullDim_top, u.shape.krullDim_eq_dimension]
    exact_mod_cast (hu.trans_le j.zero_le)
  refine Within.equiv_of_image_eq ((Within.refl u).grayTensor (Within.boundary z k α))
    (Within.boundary _ k α) ?_
  rw [Within.image_grayTensor, Within.image_refl, Within.image_boundary,
    Within.image_boundary_grayTensor]
  refine congrArg _ (le_antisymm (le_iSup₂_of_le 0 k.zero_le ?_) (iSup₂_le fun i hi => ?_))
  · rw [hu', Nat.sub_zero, Nat.bodd_zero, Bool.false_xor]
  · rw [hu']
    refine LowerSet.prod_mono le_rfl ?_
    rcases i with _ | i
    · rw [Nat.sub_zero, Nat.bodd_zero, Bool.false_xor]
    · exact z.shape.isMolecule.isGlobular.boundary_le_boundary (by omega) _ _

namespace CtxExpr.Typed

variable {A : Set (RoundPastingDiagram X)}

private theorem exists_of_side {Z W : DiagSet.{u}} {A : Set (RoundPastingDiagram Z)}
    {C : Set (RoundPastingDiagram W)} (T : PastingDiagram Z → PastingDiagram W) (L : ℕ → ℕ)
    (hside : ∀ {H : PdHom Z} (α : Bool) {v₀ : PastingDiagram Z} (w : RoundPastingDiagram Z),
      w ∈ A → ∀ (_ : w.dim = H.k + 1) {V : PastingDiagram Z} (ι : Within V v₀)
      (hι : v₀.shape.ogp.IsRewritableSubmolecule ι.image ⊤) (h : (w.boundary H.k (!α)).Equiv V),
      v₀.Equiv (H.side α) → ∀ {u : PastingDiagram Z}, InHom H u →
        ∃ G : CtxExpr W, G.Typed C True ((T u).homAt (L u.dim))
          ((T ((CtxExpr.side α w.toPastingDiagram H.k ι hι.isSubmoleculeOf h).app u)).homAt
            (L u.dim)) ∧
          (G.app (T u)).Equiv
            (T ((CtxExpr.side α w.toPastingDiagram H.k ι hι.isSubmoleculeOf h).app u)))
    {H H' : PdHom Z} {F : CtxExpr Z} (hF : F.Typed A True H H') {u : PastingDiagram Z}
    (hu : InHom H u) :
    ∃ G : CtxExpr W, G.Typed C True ((T u).homAt (L u.dim)) ((T (F.app u)).homAt (L u.dim)) ∧
      (G.app (T u)).Equiv (T (F.app u)) := by
  induction hF generalizing u with
  | side α w hw hdw ι hι h hs _ => exact hside α w hw hdw ι hι h hs hu
  | id _ => exact ⟨.id, .id (.refl _), .refl _⟩
  | @comp H H' H'' s t ht₁ _ ih₁ ih₂ =>
    obtain ⟨G₁, hG₁, e₁⟩ := ih₁ hu
    obtain ⟨G₂, hG₂, e₂⟩ := ih₂ (ht₁.mapsInto u hu)
    rw [ht₁.ctxLaws.dim_eq u hu] at hG₂
    exact ⟨.comp G₂ G₁, .comp hG₁ hG₂, (CtxExpr.app_equiv G₂ e₁).trans e₂⟩
  | promote _ hk _ _ _ _ ih => exact ih (hu.promote (by omega))

private theorem exists_grayTensor_left_side {H : PdHom X} (α : Bool) {v₀ : PastingDiagram X}
    (w : RoundPastingDiagram X) (hw : w ∈ A) (hdw : w.dim = H.k + 1) {V : PastingDiagram X}
    (ι : Within V v₀) (hι : v₀.shape.ogp.IsRewritableSubmolecule ι.image ⊤)
    (h : (w.boundary H.k (!α)).Equiv V) (hs : v₀.Equiv (H.side α)) {u : PastingDiagram X}
    (hu : InHom H u) (v : RoundPastingDiagram Y) :
    ∃ G : CtxExpr (grayTensor X Y),
      G.Typed (Set.image2 RoundPastingDiagram.grayTensor A Set.univ) True
        ((u.grayTensor v.toPastingDiagram).homAt (u.dim + v.dim - 1))
        ((((CtxExpr.side α w.toPastingDiagram H.k ι hι.isSubmoleculeOf h).app u).grayTensor
          v.toPastingDiagram).homAt (u.dim + v.dim - 1)) ∧
      (G.app (u.grayTensor v.toPastingDiagram)).Equiv
        (((CtxExpr.side α w.toPastingDiagram H.k ι hι.isSubmoleculeOf h).app u).grayTensor
          v.toPastingDiagram) := by
  have hsu : (u.boundary H.k α).Equiv v₀ := (hu.side α).trans hs.symm
  have hocc := isSubmoleculeOf_image_sideOcc α H.k ι hι.isSubmoleculeOf hsu
  have happ : (CtxExpr.side α w.toPastingDiagram H.k ι hι.isSubmoleculeOf h).app u =
      pasteAtBoundary w.toPastingDiagram u H.k α (sideOcc α H.k ι hsu) hocc h :=
    sidePaste_of hsu
  rw [happ]
  set m := pasteAtBoundary w.toPastingDiagram u H.k α (sideOcc α H.k ι hsu) hocc h
  have hlt := hu.lt_dim
  have hdm : m.dim = u.dim :=
    (dim_pasteAtBoundary _ _ _ _ _ _ _).trans (max_eq_right (by rw [hdw]; exact hlt))
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, u.dim + v.dim = H.k + 1 + ℓ := ⟨u.dim + v.dim - (H.k + 1), by omega⟩
  obtain ⟨R, hR, hRa⟩ := Within.exists_typed_grayTensor_pasteAt
    (Within.pasteAtInl w.toPastingDiagram u H.k α (sideOcc α H.k ι hsu) hocc h)
    (Within.pasteAtInr w.toPastingDiagram u H.k α (sideOcc α H.k ι hsu) hocc h)
    (Within.isPastingAtIn_pasteAt _ _ _ _ _ hocc h) hdw v
    (A := Set.image2 RoundPastingDiagram.grayTensor A Set.univ)
    (fun _ => Set.mem_image2_of_mem hw (Set.mem_univ _)) (ℓ := ℓ) (by omega)
  rw [show u.dim + v.dim - 1 = H.k + ℓ by omega]
  refine ⟨R, hR, (CtxExpr.app_equiv R (equiv_boundary_dim _ ?_ (!α)).symm).trans
    (hRa.trans (equiv_boundary_dim _ ?_ (!α)))⟩
  · rw [dim_grayTensor]; omega
  · rw [dim_grayTensor, hdm]; omega

theorem exists_grayTensor_left {H H' : PdHom X} {F : CtxExpr X} (hF : F.Typed A True H H')
    {u : PastingDiagram X} (hu : InHom H u) (v : RoundPastingDiagram Y) :
    ∃ G : CtxExpr (grayTensor X Y),
      G.Typed (Set.image2 RoundPastingDiagram.grayTensor A Set.univ) True
        ((u.grayTensor v.toPastingDiagram).homAt (u.dim + v.dim - 1))
        (((F.app u).grayTensor v.toPastingDiagram).homAt (u.dim + v.dim - 1)) ∧
      (G.app (u.grayTensor v.toPastingDiagram)).Equiv
        ((F.app u).grayTensor v.toPastingDiagram) :=
  exists_of_side (fun a => a.grayTensor v.toPastingDiagram) (· + v.dim - 1)
    (fun α _ w hw hdw _ ι hι h hs _ hu => exists_grayTensor_left_side α w hw hdw ι hι h hs hu v)
    hF hu

theorem exists_typed_boundary_grayTensor_left {H H' : PdHom X} {F : CtxExpr X}
    (hF : F.Typed A True H H') {u : PastingDiagram X} (hu : InHom H u) (α : Bool)
    {z : RoundPastingDiagram X} (hz : z ∈ A) {k : ℕ} (hdz : z.dim = k + 1)
    (hzu : (z.boundary k α).Equiv (F.app u)) (v : RoundPastingDiagram Y) :
    ∃ G : CtxExpr (grayTensor X Y),
      G.Typed (Set.image2 RoundPastingDiagram.grayTensor A Set.univ) True
        ((u.grayTensor v.toPastingDiagram).homAt (k + v.dim - 1))
        ((z.grayTensor v).toPastingDiagram.homAt (k + v.dim - 1)) ∧
      (G.app (u.grayTensor v.toPastingDiagram)).Equiv
        ((z.grayTensor v).toPastingDiagram.boundary (k + v.dim) α) := by
  have hdu : u.dim = k := by
    rw [← hF.ctxLaws.dim_eq u hu, ← dim_eq_of_equiv hzu, dim_boundary _ (by omega)]
  obtain ⟨G, hG, e⟩ := hF.exists_grayTensor_left hu v
  rw [hdu] at hG
  have ez := Equiv.grayTensor hzu.symm (.refl v.toPastingDiagram)
  rcases hv : v.dim with _ | d
  · rw [hv, Nat.add_zero] at hG
    rw [Nat.add_zero, RoundPastingDiagram.toPastingDiagram_grayTensor]
    have e₀ := boundary_grayTensor_equiv_of_dim_eq_zero z.toPastingDiagram hv k α
    have hk := hu.lt_dim
    refine ⟨G, hG.congr_codomain (((ez.trans e₀).homAt _).trans
      ⟨rfl, equiv_boundary_boundary _ ?_ α false, equiv_boundary_boundary _ ?_ α true⟩),
      e.trans (ez.trans e₀)⟩ <;> omega
  · obtain ⟨R, hR, hRa⟩ := exists_typed_grayTensor_self z hdz (!α) v (ℓ := d)
      (A := Set.image2 RoundPastingDiagram.grayTensor A Set.univ)
      (fun _ => Set.mem_image2_of_mem hz (Set.mem_univ _)) (by omega)
    rw [Bool.not_not] at hR hRa
    rw [show k + (d + 1) - 1 = k + d by omega, show k + (d + 1) = k + 1 + d by omega]
    rw [hv, show k + (d + 1) - 1 = k + d by omega] at hG
    refine ⟨.comp R G, .comp hG (hR.congr_domain (ez.homAt _).symm),
      (CtxExpr.app_equiv R (e.trans (ez.trans (equiv_boundary_dim _ ?_ α).symm))).trans hRa⟩
    rw [dim_grayTensor, dim_boundary _ (by omega), hv]
    omega

variable {B : Set (RoundPastingDiagram Y)}

private theorem exists_grayTensor_right_side {H : PdHom Y} (α : Bool) {v₀ : PastingDiagram Y}
    (w : RoundPastingDiagram Y) (hw : w ∈ B) (hdw : w.dim = H.k + 1) {V : PastingDiagram Y}
    (ι : Within V v₀) (hι : v₀.shape.ogp.IsRewritableSubmolecule ι.image ⊤)
    (h : (w.boundary H.k (!α)).Equiv V) (hs : v₀.Equiv (H.side α)) {v : PastingDiagram Y}
    (hv : InHom H v) (u : RoundPastingDiagram X) :
    ∃ G : CtxExpr (grayTensor X Y),
      G.Typed (Set.image2 RoundPastingDiagram.grayTensor Set.univ B) True
        ((u.toPastingDiagram.grayTensor v).homAt (u.dim + v.dim - 1))
        ((u.toPastingDiagram.grayTensor
          ((CtxExpr.side α w.toPastingDiagram H.k ι hι.isSubmoleculeOf h).app v)).homAt
            (u.dim + v.dim - 1)) ∧
      (G.app (u.toPastingDiagram.grayTensor v)).Equiv (u.toPastingDiagram.grayTensor
        ((CtxExpr.side α w.toPastingDiagram H.k ι hι.isSubmoleculeOf h).app v)) := by
  have hsv : (v.boundary H.k α).Equiv v₀ := (hv.side α).trans hs.symm
  have hocc := isSubmoleculeOf_image_sideOcc α H.k ι hι.isSubmoleculeOf hsv
  have happ : (CtxExpr.side α w.toPastingDiagram H.k ι hι.isSubmoleculeOf h).app v =
      pasteAtBoundary w.toPastingDiagram v H.k α (sideOcc α H.k ι hsv) hocc h :=
    sidePaste_of hsv
  rw [happ]
  set m := pasteAtBoundary w.toPastingDiagram v H.k α (sideOcc α H.k ι hsv) hocc h
  have hlt := hv.lt_dim
  have hdm : m.dim = v.dim :=
    (dim_pasteAtBoundary _ _ _ _ _ _ _).trans (max_eq_right (by rw [hdw]; exact hlt))
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, u.dim + v.dim = H.k + 1 + ℓ := ⟨u.dim + v.dim - (H.k + 1), by omega⟩
  obtain ⟨R, hR, hRa⟩ := Within.exists_typed_grayTensor_pasteAt_right
    (Within.pasteAtInl w.toPastingDiagram v H.k α (sideOcc α H.k ι hsv) hocc h)
    (Within.pasteAtInr w.toPastingDiagram v H.k α (sideOcc α H.k ι hsv) hocc h)
    (Within.isPastingAtIn_pasteAt _ _ _ _ _ hocc h) hdw u
    (A := Set.image2 RoundPastingDiagram.grayTensor Set.univ B)
    (fun _ => Set.mem_image2_of_mem (Set.mem_univ _) hw) (ℓ := ℓ) (by omega)
  rw [show u.dim + v.dim - 1 = H.k + ℓ by omega]
  refine ⟨R, hR, (CtxExpr.app_equiv R (equiv_boundary_dim _ ?_ _).symm).trans
    (hRa.trans (equiv_boundary_dim _ ?_ _))⟩
  · rw [dim_grayTensor]; omega
  · rw [dim_grayTensor, hdm]; omega

theorem exists_grayTensor_right {H H' : PdHom Y} {F : CtxExpr Y} (hF : F.Typed B True H H')
    {v : PastingDiagram Y} (hv : InHom H v) (u : RoundPastingDiagram X) :
    ∃ G : CtxExpr (grayTensor X Y),
      G.Typed (Set.image2 RoundPastingDiagram.grayTensor Set.univ B) True
        ((u.toPastingDiagram.grayTensor v).homAt (u.dim + v.dim - 1))
        ((u.toPastingDiagram.grayTensor (F.app v)).homAt (u.dim + v.dim - 1)) ∧
      (G.app (u.toPastingDiagram.grayTensor v)).Equiv
        (u.toPastingDiagram.grayTensor (F.app v)) :=
  exists_of_side u.toPastingDiagram.grayTensor (u.dim + · - 1)
    (fun α _ w hw hdw _ ι hι h hs _ hv => exists_grayTensor_right_side α w hw hdw ι hι h hs hv u)
    hF hv

theorem exists_typed_boundary_grayTensor_right {H H' : PdHom Y} {F : CtxExpr Y}
    (hF : F.Typed B True H H') {v : PastingDiagram Y} (hv : InHom H v) (α : Bool)
    {z : RoundPastingDiagram Y} (hz : z ∈ B) {k : ℕ} (hdz : z.dim = k + 1)
    (hzv : (z.boundary k α).Equiv (F.app v)) (u : RoundPastingDiagram X) :
    ∃ G : CtxExpr (grayTensor X Y),
      G.Typed (Set.image2 RoundPastingDiagram.grayTensor Set.univ B) True
        ((u.toPastingDiagram.grayTensor v).homAt (u.dim + k - 1))
        ((u.grayTensor z).toPastingDiagram.homAt (u.dim + k - 1)) ∧
      (G.app (u.toPastingDiagram.grayTensor v)).Equiv
        ((u.grayTensor z).toPastingDiagram.boundary (u.dim + k) (xor u.dim.bodd α)) := by
  have hdv : v.dim = k := by
    rw [← hF.ctxLaws.dim_eq v hv, ← dim_eq_of_equiv hzv, dim_boundary _ (by omega)]
  obtain ⟨G, hG, e⟩ := hF.exists_grayTensor_right hv u
  rw [hdv] at hG
  have ez := Equiv.grayTensor (.refl u.toPastingDiagram) hzv.symm
  rcases hu : u.dim with _ | d
  · rw [hu, Nat.zero_add] at hG
    rw [Nat.zero_add, Nat.bodd_zero, Bool.false_xor,
      RoundPastingDiagram.toPastingDiagram_grayTensor]
    have e₀ := grayTensor_boundary_equiv_of_dim_eq_zero hu z.toPastingDiagram k α
    have hk := hv.lt_dim
    refine ⟨G, hG.congr_codomain (((ez.trans e₀).homAt _).trans
      ⟨rfl, equiv_boundary_boundary _ ?_ α false, equiv_boundary_boundary _ ?_ α true⟩),
      e.trans (ez.trans e₀)⟩ <;> omega
  · obtain ⟨R, hR, hRa⟩ := exists_typed_grayTensor_self_right u z hdz (!α) (ℓ := d)
      (A := Set.image2 RoundPastingDiagram.grayTensor Set.univ B)
      (fun _ => Set.mem_image2_of_mem (Set.mem_univ _) hz) (by omega)
    rw [Bool.not_not] at hR hRa
    rw [hu, show d + 1 + k - 1 = k + d by omega] at hG
    rw [show d + 1 + k - 1 = k + d by omega, show d + 1 + k = k + 1 + d by omega, Nat.bodd_succ,
      Bool.not_xor, ← Bool.xor_not]
    refine ⟨.comp R G, .comp hG (hR.congr_domain (ez.homAt _).symm),
      (CtxExpr.app_equiv R (e.trans (ez.trans (equiv_boundary_dim _ ?_ _).symm))).trans hRa⟩
    rw [dim_grayTensor, dim_boundary _ (by omega), hu]
    omega

end CtxExpr.Typed

end Atoms.Diagrammatic
