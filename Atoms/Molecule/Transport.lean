import Atoms.Molecule.Inclusion
import Atoms.Molecule.Molecule

universe u v

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

variable {P Q : OGP.{u}} (f : P ⟶ Q) [IsInclusion f]

theorem isGlobular_map_iff (U : LowerSet P) :
    Q.IsGlobular (map f U) ↔ P.IsGlobular U := by
  simp only [IsGlobular, ← map_boundary f, map_inj f]

theorem isRound_map_iff (U : LowerSet P) :
    Q.IsRound (map f U) ↔ P.IsRound U := by
  refine ⟨fun h => ⟨(isGlobular_map_iff f U).1 h.isGlobular, fun hd => ?_, fun n hn => ?_⟩,
    fun h => ⟨(isGlobular_map_iff f U).2 h.isGlobular, fun hd => ?_, fun n hn => ?_⟩⟩
  · have h0 := h.inf_boundary_zero (by rwa [krullDim_map f])
    rwa [← map_boundary f, ← map_boundary f, ← map_inf f, map_eq_bot_iff f] at h0
  · have hs := h.inf_boundary_succ n (by rwa [krullDim_map f])
    rwa [← map_boundary f, ← map_boundary f, ← map_inf f, ← map_boundaryFull f,
      map_inj f] at hs
  · rw [krullDim_map f] at hd
    rw [← map_boundary f, ← map_boundary f, ← map_inf f, map_eq_bot_iff f]
    exact h.inf_boundary_zero hd
  · rw [krullDim_map f] at hn
    rw [← map_boundary f, ← map_boundary f, ← map_inf f, ← map_boundaryFull f,
      map_inj f]
    exact h.inf_boundary_succ n hn

theorem isPastingIn_map_iff (k : ℕ) (V W U : LowerSet P) :
    Q.IsPastingIn k (map f V) (map f W) (map f U) ↔ P.IsPastingIn k V W U := by
  refine ⟨fun h => ⟨map_injective f ?_, map_injective f ?_, map_injective f ?_⟩,
    fun h => ⟨?_, ?_, ?_⟩⟩
  · rw [map_sup f]
    exact h.sup_eq
  · rw [map_inf f, map_boundary f]
    exact h.inf_eq_output
  · rw [map_inf f, map_boundary f]
    exact h.inf_eq_input
  · rw [← map_sup f, h.sup_eq]
  · rw [← map_inf f, h.inf_eq_output, map_boundary f]
  · rw [← map_inf f, h.inf_eq_input, map_boundary f]

theorem isMoleculeIn_map {U : LowerSet P} (h : IsMoleculeIn P U) :
    IsMoleculeIn Q (map f U) := by
  induction h with
  | point x hx =>
    rw [map_Iic f]
    refine .point _ fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := (isMorphism f).fibration hz
    exact (isMorphism f).monotone (hx hy)
  | atom t hround _ ih =>
    have hr : Q.IsRound (map f (.Iic t)) := (isRound_map_iff f _).2 hround
    have hb (α : Bool) : IsMoleculeIn Q (Q.bdry (map f (.Iic t)) α) := map_bdry f _ α ▸ ih α
    rw [map_Iic f] at hr hb ⊢
    exact .atom (f t) hr hb
  | paste k V W U hp _ _ hk ihV ihW =>
    exact .paste k _ _ _ ((isPastingIn_map_iff f k V W U).2 hp) ihV ihW
      (by rwa [krullDim_map f, krullDim_map f])

theorem isMoleculeIn_of_map {U : LowerSet P}
    (h : IsMoleculeIn Q (map f U)) : IsMoleculeIn P U := by
  suffices key : ∀ X, IsMoleculeIn Q X → ∀ U, map f U = X → IsMoleculeIn P U from
    key _ h U rfl
  intro X hX
  induction hX with
  | point x hx =>
    intro U hU
    have hxU : x ∈ map f U := by
      rw [hU]
      exact LowerSet.mem_Iic_iff.2 le_rfl
    obtain ⟨y, -, rfl⟩ := hxU
    rw [← map_Iic f, map_inj f] at hU
    subst hU
    exact .point y fun z hz => (IsInclusion.le_iff f).1 (hx ((isMorphism f).monotone hz))
  | atom s hround _ ih =>
    intro U hU
    have hsU : s ∈ map f U := by
      rw [hU]
      exact LowerSet.mem_Iic_iff.2 le_rfl
    obtain ⟨y, -, rfl⟩ := hsU
    rw [← map_Iic f, map_inj f] at hU
    subst hU
    refine .atom y ((isRound_map_iff f _).1 (by rw [map_Iic]; exact hround)) fun α => ih α _ ?_
    rw [map_bdry, map_Iic]
  | paste k V W X hp _ _ hk ihV ihW =>
    intro U hU
    subst hU
    obtain ⟨V', -, rfl⟩ := exists_map_eq_of_le f hp.left_le
    obtain ⟨W', -, rfl⟩ := exists_map_eq_of_le f hp.right_le
    exact .paste k V' W' U ((isPastingIn_map_iff f k V' W' U).1 hp) (ihV V' rfl) (ihW W' rfl)
      (by rwa [krullDim_map f, krullDim_map f] at hk)

theorem isMoleculeIn_map_iff (U : LowerSet P) :
    IsMoleculeIn Q (map f U) ↔ IsMoleculeIn P U :=
  ⟨isMoleculeIn_of_map f, isMoleculeIn_map f⟩

theorem isMolecule_iff_of_iso {P Q : OGP.{u}} (e : P ≅ Q) : IsMolecule Q ↔ IsMolecule P := by
  have h := isMoleculeIn_map_iff e.hom ⊤
  rwa [map_top_of_isIso] at h

theorem isRound_top_iff_of_iso {P Q : OGP.{u}} (e : P ≅ Q) : Q.IsRound ⊤ ↔ P.IsRound ⊤ := by
  have h := isRound_map_iff e.hom ⊤
  rwa [map_top_of_isIso] at h

theorem isMolecule_restrict_iff (U : LowerSet P) :
    IsMolecule (P.restrict U) ↔ IsMoleculeIn P U := by
  have h := isMoleculeIn_map_iff (incl U) ⊤
  rwa [map_incl_top, Iff.comm] at h

section Transport

variable {A : OGP.{u}} {B : OGP.{v}} {g : A → B} {U : LowerSet A} {X : LowerSet B}

private theorem IsMorphism.le_of_apply_le_of_injOn (hg : IsMorphism g) (hi : InjOn g U)
    {a b : A} (ha : a ∈ U) (hb : b ∈ U) (h : g a ≤ g b) : a ≤ b := by
  obtain ⟨a', ha', he⟩ := hg.fibration h
  rwa [hi (U.lower ha' hb) ha he] at ha'

private theorem IsMorphism.apply_mem_cofaces_iff_of_injOn (hg : IsMorphism g) (hi : InjOn g U)
    {β : Bool} {x z : A} (hx : x ∈ U) (hz : z ∈ U) :
    g z ∈ B.cofaces β (g x) ↔ z ∈ A.cofaces β x := by
  refine ⟨fun h => ?_, fun h => (hg.bijOn_faces z β).mapsTo h⟩
  obtain ⟨x', hx', he⟩ := (hg.bijOn_faces z β).surjOn h
  rwa [hi (U.lower hx'.1.le hz) hx he] at hx'

theorem eq_of_image_eq_of_injOn (hi : InjOn g U) {V W : LowerSet A} (hV : V ≤ U)
    (hW : W ≤ U) (h : g '' (V : Set A) = g '' W) : V = W :=
  SetLike.coe_injective ((hi.image_eq_image_iff hV hW).1 h)

section

variable (hg : IsMorphism g) (hi : InjOn g U) (hX : (X : Set B) = g '' U)
include hg hi hX

private theorem IsMorphism.image_facesIn_of_injOn (n : ℕ) (α : Bool) :
    g '' A.facesIn U n α = B.facesIn X n α := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxU, hxn, hd⟩, rfl⟩
    refine ⟨hX ▸ mem_image_of_mem g hxU, by rw [hg.grade_eq, hxn], disjoint_left.2 ?_⟩
    intro w hw hwX
    rw [hX] at hwX
    obtain ⟨z, hz, rfl⟩ := hwX
    exact disjoint_left.1 hd ((hg.apply_mem_cofaces_iff_of_injOn hi hxU hz).1 hw) hz
  · rintro ⟨hyX, hyn, hd⟩
    rw [hX] at hyX
    obtain ⟨x, hxU, rfl⟩ := hyX
    refine ⟨x, ⟨hxU, by rw [← hg.grade_eq, hyn], disjoint_left.2 fun z hz hzU => ?_⟩, rfl⟩
    exact disjoint_left.1 hd ((hg.apply_mem_cofaces_iff_of_injOn hi hxU hzU).2 hz)
      (hX ▸ mem_image_of_mem g hzU)

private theorem IsMorphism.maximal_apply_iff_of_injOn {x : A} (hx : x ∈ U) :
    Maximal (· ∈ X) (g x) ↔ Maximal (· ∈ U) x := by
  have hmem {z : A} (hz : z ∈ U) : g z ∈ X := by
    rw [← SetLike.mem_coe, hX]
    exact mem_image_of_mem g hz
  refine ⟨fun h => ⟨hx, fun z hz hxz =>
    hg.le_of_apply_le_of_injOn hi hz hx (h.2 (hmem hz) (hg.monotone hxz))⟩,
    fun h => ⟨hmem hx, fun w hw hxw => ?_⟩⟩
  obtain ⟨z, hz, rfl⟩ : w ∈ g '' (U : Set A) := hX ▸ hw
  exact hg.monotone (h.2 hz (hg.le_of_apply_le_of_injOn hi hx hz hxw))

theorem IsMorphism.image_boundary_of_injOn (n : ℕ) (α : Bool) :
    g '' (A.boundary U n α : Set A) = B.boundary X n α := by
  have hmax : g '' {x | Maximal (· ∈ U) x ∧ grade ℕ x < n} =
      {y | Maximal (· ∈ X) y ∧ grade ℕ y < n} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
      exact ⟨(hg.maximal_apply_iff_of_injOn hi hX hx.prop).2 hx, by rwa [hg.grade_eq]⟩
    · rintro ⟨hy, hn⟩
      have hyX := hy.prop
      rw [← SetLike.mem_coe, hX] at hyX
      obtain ⟨x, hxU, rfl⟩ := hyX
      exact ⟨x, ⟨(hg.maximal_apply_iff_of_injOn hi hX hxU).1 hy, by rwa [← hg.grade_eq]⟩, rfl⟩
  rw [boundary, boundary, hg.fibration.image_lowerClosure hg.monotone, image_union,
    hg.image_facesIn_of_injOn hi hX, hmax]

private theorem IsMorphism.krullDim_eq_of_injOn : krullDim X = krullDim U :=
  (krullDim_eq_of_orderIso
    { toEquiv := (Equiv.Set.imageOfInjOn g U hi).trans (Equiv.setCongr hX.symm),
      map_rel_iff' := fun {a b} => ⟨hg.le_of_apply_le_of_injOn hi a.2 b.2,
        fun h => hg.monotone h⟩ }).symm

private theorem IsMorphism.image_bdry_of_injOn (α : Bool) :
    g '' (A.bdry U α : Set A) = B.bdry X α := by
  rw [bdry, bdry, hg.krullDim_eq_of_injOn hi hX]
  simp only [LowerSet.coe_iSup, image_iUnion, hg.image_boundary_of_injOn hi hX]

omit hi in
private theorem IsMorphism.coe_eq_image_inf_of_injOn {S : LowerSet B} (hS : S ≤ X) :
    (S : Set B) = g '' (U ⊓ ⟨g ⁻¹' S, S.lower.preimage hg.monotone⟩ : LowerSet A) := by
  change (S : Set B) = g '' ((U : Set A) ∩ g ⁻¹' S)
  rw [image_inter_preimage, ← hX, inter_eq_right.2 (LowerSet.coe_subset_coe.2 hS)]

private theorem IsMorphism.isRound_of_injOn (h : B.IsRound X) : A.IsRound U := by
  have hb (n : ℕ) (β : Bool) := hg.image_boundary_of_injOn hi hX n β
  have hbb (n : ℕ) (β : Bool) := hg.image_boundary_of_injOn (hi.mono (boundary_le U n β))
    (hb n β).symm
  have hinf (m n : ℕ) (β γ : Bool) : g '' (A.boundary U m β ⊓ A.boundary U n γ : LowerSet A) =
      (B.boundary X m β ⊓ B.boundary X n γ : LowerSet B) := by
    rw [LowerSet.coe_inf, LowerSet.coe_inf, hi.image_inter (boundary_le U m β)
      (boundary_le U n γ), hb, hb]
  have hd := hg.krullDim_eq_of_injOn hi hX
  refine ⟨fun k n hkn α β => eq_of_image_eq_of_injOn hi
    ((boundary_le _ _ _).trans (boundary_le _ _ _)) (boundary_le _ _ _) ?_, fun h0 => ?_,
    fun n hn => eq_of_image_eq_of_injOn hi (inf_le_left.trans (boundary_le _ _ _))
      (sup_le (boundary_le _ _ _) (boundary_le _ _ _)) ?_⟩
  · rw [hbb, hb, h.isGlobular k n hkn α β]
  · refine eq_of_image_eq_of_injOn hi (inf_le_left.trans (boundary_le _ _ _)) bot_le ?_
    rw [hinf, h.inf_boundary_zero (hd ▸ h0), LowerSet.coe_bot, LowerSet.coe_bot, image_empty]
  · rw [hinf, h.inf_boundary_succ n (hd ▸ hn), boundaryFull, boundaryFull, LowerSet.coe_sup,
      LowerSet.coe_sup, image_union, hb, hb]

private theorem IsMorphism.exists_eq_Iic_of_injOn {y : B} (hy : X = LowerSet.Iic y) :
    ∃ x, g x = y ∧ U = LowerSet.Iic x := by
  have hyX : y ∈ (X : Set B) := by rw [hy]; exact LowerSet.mem_Iic_iff.2 le_rfl
  rw [hX] at hyX
  obtain ⟨x, hxU, rfl⟩ := hyX
  refine ⟨x, rfl, SetLike.ext fun z => ⟨fun hz => ?_, fun hz => U.lower hz hxU⟩⟩
  have hgz : g z ∈ (X : Set B) := hX ▸ mem_image_of_mem g hz
  rw [hy] at hgz
  exact hg.le_of_apply_le_of_injOn hi hz hxU hgz

end

theorem IsMorphism.isMoleculeIn_of_injOn (hg : IsMorphism g) (hi : InjOn g U)
    (hX : (X : Set B) = g '' U) (h : IsMoleculeIn B X) : IsMoleculeIn A U := by
  induction h generalizing U with
  | point y hy =>
    obtain ⟨x, rfl, rfl⟩ := hg.exists_eq_Iic_of_injOn hi hX rfl
    exact .point x fun z hz => hg.le_of_apply_le_of_injOn hi (LowerSet.mem_Iic_iff.2 le_rfl) hz
      (hy (hg.monotone hz))
  | atom t hround _ ih =>
    obtain ⟨x, rfl, rfl⟩ := hg.exists_eq_Iic_of_injOn hi hX rfl
    exact .atom x (hg.isRound_of_injOn hi hX hround) fun α =>
      ih α (hi.mono (show A.bdry (LowerSet.Iic x) α ≤ LowerSet.Iic x from
        iSup₂_le fun _ _ => boundary_le _ _ α))
        (hg.image_bdry_of_injOn hi hX α).symm
  | paste k V W X hp _ _ hk ihV ihW =>
    have hV := hg.coe_eq_image_inf_of_injOn hX hp.left_le
    have hW := hg.coe_eq_image_inf_of_injOn hX hp.right_le
    have hVU : U ⊓ ⟨g ⁻¹' V, V.lower.preimage hg.monotone⟩ ≤ U := inf_le_left
    have hWU : U ⊓ ⟨g ⁻¹' W, W.lower.preimage hg.monotone⟩ ≤ U := inf_le_left
    have hiV := hi.mono hVU
    have hiW := hi.mono hWU
    refine .paste k _ _ U ⟨?_, ?_, ?_⟩ (ihV hiV hV) (ihW hiW hW) ?_
    · refine eq_of_image_eq_of_injOn hi (sup_le hVU hWU) le_rfl ?_
      rw [LowerSet.coe_sup, image_union, ← hV, ← hW, ← LowerSet.coe_sup, hp.sup_eq, hX]
    · refine eq_of_image_eq_of_injOn hi (inf_le_left.trans hVU) ((boundary_le _ _ _).trans hVU) ?_
      rw [LowerSet.coe_inf, hi.image_inter hVU hWU, ← hV, ← hW,
        ← LowerSet.coe_inf, hp.inf_eq_output, hg.image_boundary_of_injOn hiV hV]
    · refine eq_of_image_eq_of_injOn hi (inf_le_left.trans hVU) ((boundary_le _ _ _).trans hWU) ?_
      rw [LowerSet.coe_inf, hi.image_inter hVU hWU, ← hV, ← hW,
        ← LowerSet.coe_inf, hp.inf_eq_input, hg.image_boundary_of_injOn hiW hW]
    · rwa [← hg.krullDim_eq_of_injOn hiV hV, ← hg.krullDim_eq_of_injOn hiW hW]

end Transport

end Atoms.Molecule.OGP
