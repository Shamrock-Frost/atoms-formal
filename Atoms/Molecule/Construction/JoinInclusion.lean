import Atoms.Molecule.Construction.JoinMap

universe u

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

def joinInclLeft (P Q : OGP.{u}) : P → join P Q :=
  fun x => ⟨((x : WithBot P), ⊥), fun h => WithBot.coe_ne_bot (congrArg Prod.fst h)⟩

def joinInclRight (P Q : OGP.{u}) : Q → join P Q :=
  fun y => ⟨(⊥, (y : WithBot Q)), fun h => WithBot.coe_ne_bot (congrArg Prod.snd h)⟩

variable {P P' Q Q' : OGP.{u}}

@[simp] theorem joinInclLeft_le_iff {x y : P} :
    joinInclLeft P Q x ≤ joinInclLeft P Q y ↔ x ≤ y :=
  join_le_iff.trans ((and_iff_left le_rfl).trans WithBot.coe_le_coe)

@[simp] theorem joinInclRight_le_iff {x y : Q} :
    joinInclRight P Q x ≤ joinInclRight P Q y ↔ x ≤ y :=
  join_le_iff.trans ((and_iff_right le_rfl).trans WithBot.coe_le_coe)

theorem injective_joinInclLeft (P Q : OGP.{u}) : Function.Injective (joinInclLeft P Q) :=
  fun _ _ h => le_antisymm (joinInclLeft_le_iff.1 h.le) (joinInclLeft_le_iff.1 h.ge)

theorem injective_joinInclRight (P Q : OGP.{u}) : Function.Injective (joinInclRight P Q) :=
  fun _ _ h => le_antisymm (joinInclRight_le_iff.1 h.le) (joinInclRight_le_iff.1 h.ge)

theorem isMorphism_joinInclLeft (P Q : OGP.{u}) : IsMorphism (joinInclLeft P Q) where
  bijOn_faces x α := by
    refine ⟨fun x' hx' => ?_, (injective_joinInclLeft P Q).injOn, fun z hz => ?_⟩
    · exact mem_faces_join.2 (mem_faces_grayProduct.2
        (.inl ⟨coe_mem_faces_augmentation.2 hx', rfl⟩))
    · obtain ⟨⟨a, b⟩, hab⟩ := z
      rcases mem_faces_grayProduct.1 (mem_faces_join.1 hz) with ⟨ha, hb⟩ | ⟨-, hb⟩
      · subst hb
        induction a using WithBot.recBotCoe with
        | bot => exact absurd rfl hab
        | coe x' => exact ⟨x', coe_mem_faces_augmentation.1 ha, rfl⟩
      · exact absurd hb.1.lt not_lt_bot

theorem isMorphism_joinInclRight (P Q : OGP.{u}) : IsMorphism (joinInclRight P Q) :=
  (isMorphism_dual_iff Nat.bodd).1
    ((isMorphism_joinInclLeft _ _).comp (isMorphism (joinSwap P Q).inv))

def join.inl (P Q : OGP.{u}) : P ⟶ join P Q :=
  ConcreteCategory.ofHom ⟨joinInclLeft P Q, isMorphism_joinInclLeft P Q⟩

@[simp] theorem join.inl_apply (P Q : OGP.{u}) (x : P) :
    join.inl P Q x = joinInclLeft P Q x := rfl

instance join.instIsInclusionInl (P Q : OGP.{u}) : IsInclusion (join.inl P Q) :=
  ⟨injective_joinInclLeft P Q⟩

def join.inr (P Q : OGP.{u}) : Q ⟶ join P Q :=
  ConcreteCategory.ofHom ⟨joinInclRight P Q, isMorphism_joinInclRight P Q⟩

@[simp] theorem join.inr_apply (P Q : OGP.{u}) (y : Q) :
    join.inr P Q y = joinInclRight P Q y := rfl

instance join.instIsInclusionInr (P Q : OGP.{u}) : IsInclusion (join.inr P Q) :=
  ⟨injective_joinInclRight P Q⟩

@[simp] theorem joinMap_joinInclLeft (f : P → P') (g : Q → Q') (x : P) :
    joinMap f g (joinInclLeft P Q x) = joinInclLeft P' Q' (f x) := rfl

@[simp] theorem joinMap_joinInclRight (f : P → P') (g : Q → Q') (y : Q) :
    joinMap f g (joinInclRight P Q y) = joinInclRight P' Q' (g y) := rfl

@[reassoc (attr := simp)]
theorem join.inl_map (f : P ⟶ P') (g : Q ⟶ Q') :
    join.inl P Q ≫ join.map f g = f ≫ join.inl P' Q' := by
  ext x
  rfl

@[reassoc (attr := simp)]
theorem join.inr_map (f : P ⟶ P') (g : Q ⟶ Q') :
    join.inr P Q ≫ join.map f g = g ≫ join.inr P' Q' := by
  ext y
  rfl

private theorem exists_isMin_le {R : OGP.{u}} (x : R) : ∃ y ≤ x, IsMin y := by
  obtain ⟨y, hyx, hy⟩ := exists_minimal_le_of_wellFoundedLT (fun _ => True) x trivial
  exact ⟨y, hyx, fun c hc => hy.2 trivial hc⟩

private theorem mem_boundary_zero_iff {R : OGP.{u}} {U : LowerSet R} {v : R} {α : Bool} :
    v ∈ R.boundary U 0 α ↔ v ∈ R.facesIn U 0 α :=
  ⟨fun hv => mem_facesIn_of_mem_boundary hv
    (Nat.eq_zero_of_le_zero (grade_le_of_mem_boundary hv)),
  fun hv => mem_boundary_of_mem_facesIn hv le_rfl⟩

private theorem mem_boundary_Iic_zero_iff {R : OGP.{u}} {z v : R} {α : Bool} :
    v ∈ R.boundary (.Iic z) 0 α ↔
      v ≤ z ∧ IsMin v ∧ ∀ w ≤ z, v ∉ R.faces (!α) w := by
  rw [mem_boundary_zero_iff]
  simp only [facesIn, mem_ofPred_eq, SetLike.mem_coe, LowerSet.mem_Iic_iff, grade_eq_zero_iff,
    disjoint_left]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun h w hw hvw => h hvw hw, fun h w hvw hw => h w hw hvw⟩

private theorem isMin_join_iff {v : join P Q} :
    IsMin v ↔
      (∃ x : P, IsMin x ∧ v = joinInclLeft P Q x) ∨
        (∃ y : Q, IsMin y ∧ v = joinInclRight P Q y) := by
  rw [← grade_eq_zero_iff]
  constructor
  · intro hd
    rw [grade_join] at hd
    obtain ⟨⟨a, b⟩, hab⟩ := v
    induction a using WithBot.recBotCoe <;> induction b using WithBot.recBotCoe
    · exact absurd rfl hab
    · exact .inr ⟨_, grade_eq_zero_iff.1 (by simpa using hd), rfl⟩
    · exact .inl ⟨_, grade_eq_zero_iff.1 (by simpa using hd), rfl⟩
    · simp at hd
  · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · rw [(isMorphism_joinInclLeft P Q).grade_eq, grade_eq_zero_iff.2 hx]
    · rw [(isMorphism_joinInclRight P Q).grade_eq, grade_eq_zero_iff.2 hy]

private def joinPair (P Q : OGP.{u}) (x : P) (y : Q) : join P Q :=
  ⟨((x : WithBot P), (y : WithBot Q)), fun h => WithBot.coe_ne_bot (congrArg Prod.fst h)⟩

private theorem joinInclRight_mem_faces_true_joinPair {x' : P} (hx' : IsMin x') (y' : Q) :
    joinInclRight P Q y' ∈ (join P Q).faces true (joinPair P Q x' y') :=
  mem_faces_join.2 (mem_faces_grayProduct.2
    (.inl ⟨bot_mem_faces_augmentation.2 ⟨hx', rfl⟩, rfl⟩))

private theorem joinInclLeft_mem_faces_true_iff {x' : P} (hx' : IsMin x') {w : join P Q} :
    joinInclLeft P Q x' ∈ (join P Q).faces true w ↔
      ∃ w' : P, x' ∈ P.faces true w' ∧ w = joinInclLeft P Q w' := by
  rw [mem_faces_join, mem_faces_grayProduct]
  dsimp only [joinInclLeft]
  constructor
  · obtain ⟨⟨c, d⟩, hcd⟩ := w
    rintro (⟨hc, hd⟩ | ⟨hc, hd⟩)
    · subst hd
      induction c using WithBot.recBotCoe with
      | bot => exact absurd rfl hcd
      | coe w' => exact ⟨w', coe_mem_faces_augmentation.1 hc, rfl⟩
    · subst hc
      dsimp only at hd
      rw [WithBot.grade_coe, grade_eq_zero_iff.2 hx'] at hd
      induction d using WithBot.recBotCoe with
      | bot => exact absurd hd.1.lt not_lt_bot
      | coe y' => exact absurd (bot_mem_faces_augmentation.1 hd).2 Bool.false_ne_true
  · rintro ⟨w', hw', rfl⟩
    exact .inl ⟨coe_mem_faces_augmentation.2 hw', rfl⟩

theorem boundary_Iic_join_zero_false (z : join P Q) (x : P) (hz : z.1.1 = (x : WithBot P)) :
    (join P Q).boundary (.Iic z) 0 false = map (join.inl P Q) (P.boundary (.Iic x) 0 false) :=
  SetLike.coe_injective (Set.ext fun v => by
    rw [SetLike.mem_coe, coe_map, mem_image, mem_boundary_Iic_zero_iff]
    constructor
    · rintro ⟨hvz, hmin, hno⟩
      rcases isMin_join_iff.1 hmin with ⟨x', hx', rfl⟩ | ⟨y', hy', rfl⟩
      · refine ⟨x', mem_boundary_Iic_zero_iff.2 ⟨?_, hx', fun w' hw' hw'f => ?_⟩, rfl⟩
        · exact WithBot.coe_le_coe.1 (hz ▸ hvz.1)
        · exact hno (joinInclLeft P Q w') ⟨hz ▸ WithBot.coe_le_coe.2 hw', bot_le⟩
            ((joinInclLeft_mem_faces_true_iff hx').2 ⟨w', hw'f, rfl⟩)
      · obtain ⟨x', hx'x, hx'⟩ := exists_isMin_le x
        exact (hno (joinPair P Q x' y') ⟨hz ▸ WithBot.coe_le_coe.2 hx'x, hvz.2⟩
          (joinInclRight_mem_faces_true_joinPair hx' y')).elim
    · rintro ⟨x', hx', rfl⟩
      obtain ⟨hx'x, hx'min, hno⟩ := mem_boundary_Iic_zero_iff.1 hx'
      refine ⟨⟨hz ▸ WithBot.coe_le_coe.2 hx'x, bot_le⟩, isMin_join_iff.2 (.inl ⟨x', hx'min, rfl⟩),
        fun w hw hwf => ?_⟩
      obtain ⟨w', hw'f, rfl⟩ := (joinInclLeft_mem_faces_true_iff hx'min).1 hwf
      exact hno w' (WithBot.coe_le_coe.1 (hz ▸ hw.1)) hw'f)

theorem boundary_Iic_join_zero_true (z : join P Q) (y : Q) (hz : z.1.2 = (y : WithBot Q)) :
    (join P Q).boundary (.Iic z) 0 true = map (join.inr P Q) (Q.boundary (.Iic y) 0 true) := by
  have h := congrArg (map (joinSwap P Q).inv)
    (boundary_Iic_join_zero_false ((joinSwap P Q).hom z) y hz)
  rw [map_boundary, map_Iic, Iso.hom_inv_id_apply, boundary_dual, ← map_comp, boundary_dual] at h
  refine h.trans (SetLike.coe_injective ?_)
  rw [coe_map, coe_map]
  rfl

theorem map_join_map_incl_top (U : LowerSet P) (V : LowerSet Q) :
    map (join.map (incl U) (incl V)) ⊤ = joinPre P Q (U.susp ×ˢ V.susp) := by
  have key (R : OGP.{u}) (W : LowerSet R) (a : WithBot R) :
      botSusp R a ∈ W.susp ↔ ∃ a' : WithBot (R.restrict W), WithBot.map (incl W) a' = a := by
    induction a using WithBot.recBotCoe with
    | bot => exact iff_of_true (pole_mem_susp W true) ⟨⊥, rfl⟩
    | coe x =>
      rw [botSusp_coe, susp_mem_susp]
      refine ⟨fun hx => ⟨WithBot.some (α := R.restrict W) ⟨x, hx⟩, rfl⟩,
        fun ⟨a', ha'⟩ => ?_⟩
      induction a' using WithBot.recBotCoe with
      | bot => exact absurd ha' WithBot.bot_ne_coe
      | coe x' =>
        obtain rfl := WithBot.coe_injective ha'
        exact x'.2
  refine SetLike.ext fun z => ⟨?_, fun h => ?_⟩
  · rintro ⟨w, -, rfl⟩
    exact ⟨(key P U _).2 ⟨w.1.1, rfl⟩, (key Q V _).2 ⟨w.1.2, rfl⟩⟩
  · obtain ⟨a, ha⟩ := (key P U _).1 h.1
    obtain ⟨b, hb⟩ := (key Q V _).1 h.2
    obtain ⟨w, -, hw⟩ := exists_joinMap_eq ha hb
    exact ⟨w, LowerSet.mem_top, hw⟩

theorem isMolecule_join_of_isEmpty_left [IsEmpty P] (hQ : IsMolecule Q) :
    IsMolecule (join P Q) := by
  have htop : map (join.inr P Q) ⊤ = ⊤ := by
    refine eq_top_iff.2 fun ⟨⟨a, b⟩, hab⟩ _ => ?_
    rcases a with _ | x
    · rcases b with _ | y
      · exact absurd rfl hab
      · exact ⟨y, LowerSet.mem_top, rfl⟩
    · exact (IsEmpty.false x).elim
  have h := isMoleculeIn_map (join.inr P Q) hQ
  rwa [htop] at h

theorem isMolecule_join_of_isEmpty_right [IsEmpty Q] (hP : IsMolecule P) :
    IsMolecule (join P Q) := by
  have : IsEmpty (dual Q Nat.bodd) := ‹IsEmpty Q›
  have h := isMolecule_join_of_isEmpty_left (P := dual Q Nat.bodd)
    ((isMoleculeIn_dual (P := P) Nat.bodd).2 hP)
  exact (isMoleculeIn_dual Nat.bodd).1 ((isMolecule_iff_of_iso (joinSwap P Q)).1 h)

end Atoms.Molecule.OGP
