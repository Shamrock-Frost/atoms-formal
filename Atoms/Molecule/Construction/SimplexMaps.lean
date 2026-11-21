import Atoms.Molecule.Construction.SimplexVertices
import Atoms.Molecule.Construction.JoinAssociativity
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

universe u

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

def simplexMap {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) :
    simplex.{u} m → simplex.{u} n :=
  fun x => simplexCell n ((simplexVertices m x).image f) ((simplexVertices_nonempty m x).image f)

@[simp] theorem simplexVertices_simplexMap {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (x : simplex.{u} m) :
    simplexVertices n (simplexMap f x) = (simplexVertices m x).image f :=
  simplexVertices_simplexCell n _ _

theorem simplexMap_eq_iff {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (x : simplex.{u} m) (y : simplex.{u} n) :
    simplexMap f x = y ↔ simplexVertices n y = (simplexVertices m x).image f :=
  ⟨fun h => h ▸ (simplexVertices_simplexMap f x),
    fun h => simplexVertices_injective n ((simplexVertices_simplexMap f x).trans h.symm)⟩

theorem monotone_simplexMap {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) :
    Monotone (simplexMap.{u} f) :=
  fun _ _ h => (simplexVertices_subset_iff n).1 (by
    rw [simplexVertices_simplexMap, simplexVertices_simplexMap]
    exact Finset.image_subset_image ((simplexVertices_subset_iff m).2 h))

theorem simplexMap_id (m : ℕ) (x : simplex.{u} m) :
    simplexMap (OrderHom.id : Fin (m + 1) →o Fin (m + 1)) x = x :=
  (simplexMap_eq_iff _ x x).2 (by simp)

theorem simplexMap_comp {m n k : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (n + 1) →o Fin (k + 1)) (x : simplex.{u} m) :
    simplexMap (g.comp f) x = simplexMap g (simplexMap f x) := by
  rw [simplexMap_eq_iff, simplexVertices_simplexMap, simplexVertices_simplexMap,
    Finset.image_image]
  rfl

theorem exists_simplexMap_eq_of_le {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    {x : simplex.{u} m} {w : simplex.{u} n} (h : w ≤ simplexMap f x) :
    ∃ y ≤ x, simplexMap f y = w := by
  have hsub := (simplexVertices_subset_iff n).2 h
  rw [simplexVertices_simplexMap] at hsub
  set T := (simplexVertices m x).filter fun v => f v ∈ simplexVertices n w
  have hT : T.image f = simplexVertices n w := by
    rw [← Finset.filter_image (p := (· ∈ simplexVertices n w)), Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.2 hsub]
  have hTne : T.Nonempty := Finset.image_nonempty.1 (hT ▸ simplexVertices_nonempty n w)
  refine ⟨simplexCell m T hTne, (simplexVertices_subset_iff m).1 ?_,
    (simplexMap_eq_iff f _ w).2 (by rw [simplexVertices_simplexCell, hT])⟩
  rw [simplexVertices_simplexCell]
  exact Finset.filter_subset _ _

theorem injective_simplexMap_of_injective {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (hf : Function.Injective f) : Function.Injective (simplexMap.{u} f) := by
  intro x y h
  apply simplexVertices_injective m
  apply Finset.image_injective hf
  rw [← simplexVertices_simplexMap, ← simplexVertices_simplexMap, h]

theorem mem_faces_simplex_iff (n : ℕ) {x y : simplex.{u} n} {α : Bool} :
    y ∈ (simplex.{u} n).faces α x ↔
      ∃ v ∈ simplexVertices n x,
        simplexVertices n y = (simplexVertices n x).erase v ∧
        α = decide (((simplexVertices n x).filter fun w => w < v).card % 2 = 0) := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨v, hv, hy⟩ := exists_simplexVertices_eq_erase_of_covBy h.1
    exact ⟨v, hv, hy, h.2.symm.trans (orient_simplex_erase n hv hy h.1)⟩
  · rintro ⟨v, hv, hy, rfl⟩
    exact mem_faces_simplex_of_erase n hv hy

theorem simplexMap_mem_faces_iff_of_injective {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (hf : Function.Injective f) {x y : simplex.{u} m} {α : Bool} :
    simplexMap f y ∈ (simplex.{u} n).faces α (simplexMap f x) ↔ y ∈ (simplex.{u} m).faces α x := by
  have hmono := f.monotone.strictMono_of_injective hf
  rw [mem_faces_simplex_iff, mem_faces_simplex_iff, simplexVertices_simplexMap,
    simplexVertices_simplexMap, Finset.exists_mem_image]
  refine exists_congr fun v => and_congr_right fun hv => ?_
  rw [← Finset.image_erase hf, (Finset.image_injective hf).eq_iff, Finset.filter_image,
    Finset.card_image_of_injective _ hf,
    Finset.filter_congr (fun w _ => hmono.lt_iff_lt (a := w) (b := v))]

theorem isMorphism_simplexMap_of_injective {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (hf : Function.Injective f) : IsMorphism (simplexMap.{u} f) := by
  refine ⟨fun x α => ⟨fun y hy => (simplexMap_mem_faces_iff_of_injective f hf).2 hy,
    (injective_simplexMap_of_injective f hf).injOn, fun z hz => ?_⟩⟩
  obtain ⟨y, -, rfl⟩ := exists_simplexMap_eq_of_le f hz.1.le
  exact ⟨y, (simplexMap_mem_faces_iff_of_injective f hf).1 hz, rfl⟩

def simplex.mapOfInjective {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (hf : Function.Injective f) : simplex.{u} m ⟶ simplex.{u} n :=
  ConcreteCategory.ofHom ⟨simplexMap f, isMorphism_simplexMap_of_injective f hf⟩

@[simp] theorem simplex.mapOfInjective_apply {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (hf : Function.Injective f) (x : simplex.{u} m) :
    simplex.mapOfInjective f hf x = simplexMap f x := rfl

instance {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (hf : Function.Injective f) :
    IsInclusion (simplex.mapOfInjective.{u} f hf) :=
  ⟨injective_simplexMap_of_injective f hf⟩

theorem surjective_simplexMap_of_surjective {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (hf : Function.Surjective f) : Function.Surjective (simplexMap.{u} f) := by
  intro y
  set S := simplexVertices n y
  set T := Finset.univ.filter (fun i => f i ∈ S)
  have himage : T.image f = S := by
    rw [← Finset.filter_image (p := (· ∈ S)), Finset.filter_mem_eq_inter,
      Finset.image_univ_of_surjective hf, Finset.univ_inter]
  have hT : T.Nonempty := by
    obtain ⟨b, hb⟩ := simplexVertices_nonempty n y
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ a, hb⟩⟩
  obtain ⟨x, hx⟩ := exists_simplexVertices_eq.{u} m T hT
  exact ⟨x, (simplexMap_eq_iff f x y).2 (by rw [hx, himage])⟩

theorem monotone_constPoint (P : OGP.{u}) : Monotone (fun _ : P => (⊤ : point.{u})) :=
  fun _ _ _ => le_top

theorem isMap_constPoint {P : OGP.{u}} (hP : IsRDC P) :
    IsMap (fun _ : P => (⊤ : point.{u})) := by
  refine ⟨Topology.IsUpperSet.isClosedMap_iff_fibration.2 fun x w _ =>
    ⟨x, le_rfl, le_antisymm le_top (isMin_point w le_top)⟩,
    fun x n α => ⟨fun _ _ => ?_, fun y _ => ?_⟩⟩
  · obtain ⟨w, hw⟩ := ((isRDC_point ⊤).boundary n α).nonempty
    have hw' : w = ⊤ := le_antisymm le_top (isMin_point w le_top)
    rwa [hw'] at hw
  · have hpre : (fun _ : P => (⊤ : point.{u})) ⁻¹' Ici y = univ :=
      eq_univ_of_forall fun _ => mem_preimage.2 (mem_Ici.2 le_top)
    rw [hpre, inter_univ]
    exact ((hP x).boundary n α).isConnected

theorem functor_isFibered_constPoint (P : OGP.{u}) :
    (monotone_constPoint P).functor.IsFibered :=
  (Monotone.functor_isFibered_iff _).2 fun x w _ =>
    ⟨x, le_rfl, le_antisymm le_top (isMin_point w le_top), fun _ hz _ => hz⟩

theorem botVertices_map_simplexMap {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (a : WithBot (simplex.{u} m)) :
    botVertices n (WithBot.map (simplexMap f) a) = (botVertices m a).image f := by
  induction a using WithBot.recBotCoe with
  | bot =>
    change botVertices n ⊥ = (botVertices m ⊥).image f
    rw [botVertices_bot, botVertices_bot, Finset.image_empty]
  | coe x => exact simplexVertices_simplexMap f x

theorem simplexMap_eq_of_botVertices {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (g : simplex.{u} m → simplex.{u} n)
    (h : ∀ x, botVertices n (g x : WithBot (simplex.{u} n)) =
      (botVertices m (x : WithBot (simplex.{u} m))).image f) :
    (simplexMap f : simplex.{u} m → simplex.{u} n) = g :=
  funext fun x => (simplexMap_eq_iff f x (g x)).2 (h x)

theorem botVertices_succ (n : ℕ) (a : WithBot (simplex.{u} (n + 1))) :
    botVertices (n + 1) a =
      pairVertices n (joinBotFst (U := point.{u}) (V := simplex.{u} n) a)
        (joinBotSnd (U := point.{u}) (V := simplex.{u} n) a) := by
  induction a using WithBot.recBotCoe with
  | bot => exact (botVertices_bot _).trans (pairVertices_bot_bot n).symm
  | coe p => rfl

theorem simplexMap_predAbove_succ (n : ℕ) (j : Fin (n + 1)) :
    (simplexMap (Fin.predAboveOrderHom j.succ) :
      simplex.{u} (n + 2) → simplex.{u} (n + 1)) =
      joinMap (P := point.{u}) (P' := point.{u}) (Q := simplex.{u} (n + 1)) (Q' := simplex.{u} n)
        id (simplexMap (Fin.predAboveOrderHom j)) := by
  refine simplexMap_eq_of_botVertices _ _ fun x => ?_
  change pairVertices n (WithBot.map id x.1.1)
      (WithBot.map (simplexMap (Fin.predAboveOrderHom j)) x.1.2) =
    (pairVertices (n + 1) x.1.1 x.1.2).image _
  rw [WithBot.map_id, id_eq]
  refine (image_pairVertices (g := Fin.predAbove j) (h := Fin.predAbove j.succ) ?_
    (Fin.succ_predAbove_succ j) x.1.1
    (botVertices_map_simplexMap _ x.1.2)).symm
  exact Fin.predAbove_of_le_castSucc _ _ (Fin.zero_le _)

theorem botVertices_joinMap_joinAssocInv (n : ℕ) (x : simplex.{u} (n + 2)) :
    botVertices (n + 1)
      (WithBot.some (α := simplex.{u} (n + 1))
        (joinMap (P := join point.{u} point.{u}) (P' := point.{u})
          (Q := simplex.{u} n) (Q' := simplex.{u} n)
          (fun _ => (⊤ : point.{u})) id
          ((joinAssoc point.{u} point.{u} (simplex.{u} n)).inv x))) =
      (botVertices (n + 2) (x : WithBot (simplex.{u} (n + 2)))).image (Fin.predAbove 0) := by
  have hA := joinLeftComponents_joinAssocInvFun point.{u} point.{u} (simplex.{u} n) x
  simp only [joinLeftComponents, joinRightComponents, Prod.mk.injEq] at hA
  obtain ⟨h1, h2, h3⟩ := hA
  change pairVertices n
      (WithBot.map (fun _ => (⊤ : point.{u}))
        ((joinAssocInvFun point.{u} point.{u} (simplex.{u} n) x).1.1))
      (WithBot.map id ((joinAssocInvFun point.{u} point.{u} (simplex.{u} n) x).1.2)) =
    (pairVertices (n + 1) x.1.1 x.1.2).image (Fin.predAbove 0)
  rw [WithBot.map_id, id_eq, h3]
  have hd : ∀ t : WithBot (join point.{u} point.{u}),
      WithBot.map (fun _ => (⊤ : point.{u})) t ≠ ⊥ ↔
        joinBotFst t ≠ ⊥ ∨ joinBotSnd t ≠ ⊥ := by
    intro t
    rw [ne_eq, WithBot.map_eq_bot_iff, joinBot_eq_iff, joinBotFst_bot, joinBotSnd_bot]
    tauto
  refine (image_predAbove_zero_pairVertices n (botVertices_succ n x.1.2)
    ((hd _).trans ?_)).symm
  rw [h1, h2]

theorem simplexMap_predAbove_zero (n : ℕ) :
    (simplexMap (Fin.predAboveOrderHom 0) :
      simplex.{u} (n + 2) → simplex.{u} (n + 1)) =
      fun x => joinMap (P := join point.{u} point.{u}) (P' := point.{u})
        (Q := simplex.{u} n) (Q' := simplex.{u} n)
        (fun _ => (⊤ : point.{u})) id
        ((joinAssoc point.{u} point.{u} (simplex.{u} n)).inv x) :=
  simplexMap_eq_of_botVertices _ _ fun x => botVertices_joinMap_joinAssocInv n x

private theorem functor_isFibered_of_eq {α β : Type*} [Preorder α] [Preorder β]
    {f g : α → β} {hf : Monotone f} (hfib : hf.functor.IsFibered) (hg : Monotone g) (h : f = g) :
    hg.functor.IsFibered := by
  subst h
  exact hfib

private theorem simplexMap_eq_const (f : Fin 2 →o Fin 1) :
    (simplexMap f : simplex.{u} 1 → simplex.{u} 0) = fun _ => (⊤ : point.{u}) :=
  funext fun _ => simplexVertices_injective 0 rfl

theorem isMap_simplexMap_predAbove (n : ℕ) (i : Fin (n + 1)) :
    IsMap (simplexMap.{u} (Fin.predAboveOrderHom i)) := by
  induction n with
  | zero =>
    rw [simplexMap_eq_const]
    exact isMap_constPoint (isRDC_simplex 1)
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      rw [simplexMap_predAbove_zero]
      exact (isMap_of_isInclusion (joinAssoc point.{u} point.{u} (simplex.{u} n)).inv).comp
        (isMap_joinMap (isRDC_simplex 1) (isRDC_simplex 0) (isRDC_simplex n) (isRDC_simplex n)
          (isMap_constPoint (isRDC_simplex 1)) (IsMap.id _))
    | succ j =>
      rw [simplexMap_predAbove_succ]
      exact isMap_joinMap (isRDC_simplex 0) (isRDC_simplex 0) (isRDC_simplex (n + 1))
        (isRDC_simplex n) (IsMap.id _) (ih j)

theorem functor_isFibered_simplexMap_predAbove (n : ℕ) (i : Fin (n + 1)) :
    (monotone_simplexMap.{u} (Fin.predAboveOrderHom i)).functor.IsFibered := by
  induction n with
  | zero =>
    exact functor_isFibered_of_eq (functor_isFibered_constPoint (simplex.{u} 1)) _
      (simplexMap_eq_const _).symm
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      have := (isLocalEmbedding_of_isInclusion
        (joinAssoc point.{u} point.{u} (simplex.{u} n)).inv).functor_isFibered
      have := functor_isFibered_constPoint (join point.{u} point.{u})
      have := Monotone.functor_isFibered_id (α := simplex.{u} n)
      have := functor_isFibered_joinMap (monotone_constPoint (join point.{u} point.{u}))
        (monotone_id (α := simplex.{u} n))
      have hfib := Monotone.functor_isFibered_comp
        (isLocalEmbedding_of_isInclusion
          (joinAssoc point.{u} point.{u} (simplex.{u} n)).inv).monotone
        (monotone_joinMap (monotone_constPoint (join point.{u} point.{u}))
          (monotone_id (α := simplex.{u} n)))
      exact functor_isFibered_of_eq hfib _ (simplexMap_predAbove_zero n).symm
    | succ j =>
      have := Monotone.functor_isFibered_id (α := point.{u})
      have := ih j
      have hfib := functor_isFibered_joinMap (monotone_id (α := point.{u}))
        (monotone_simplexMap (Fin.predAboveOrderHom j))
      exact functor_isFibered_of_eq hfib _ (simplexMap_predAbove_succ n j).symm

private theorem exists_simplexMap_eq_comp {m n : ℕ} (f : Fin (m + 2) →o Fin (n + 1))
    (hf : ¬Function.Injective f) : ∃ (i : Fin (m + 1)) (θ : Fin (m + 1) →o Fin (n + 1)),
      simplexMap.{u} f = simplexMap θ ∘ simplexMap (Fin.predAboveOrderHom i) := by
  obtain ⟨i, θ, hθ⟩ := SimplexCategory.eq_σ_comp_of_not_injective (SimplexCategory.mkHom f) hf
  have hfac : f = θ.toOrderHom.comp (Fin.predAboveOrderHom i) := by
    have h := congrArg SimplexCategory.Hom.toOrderHom hθ
    rwa [SimplexCategory.comp_toOrderHom] at h
  exact ⟨i, θ.toOrderHom, funext fun x => by rw [hfac, Function.comp_apply, simplexMap_comp]⟩

theorem isMap_simplexMap {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) :
    IsMap (simplexMap.{u} f) := by
  induction m generalizing n with
  | zero =>
    have hf : Function.Injective f := fun a b _ => Subsingleton.elim (α := Fin 1) a b
    exact isMap_of_isInclusion (simplex.mapOfInjective f hf)
  | succ m ih =>
    by_cases hf : Function.Injective f
    · exact isMap_of_isInclusion (simplex.mapOfInjective f hf)
    · obtain ⟨i, θ, hmap⟩ := exists_simplexMap_eq_comp f hf
      rw [hmap]
      exact (isMap_simplexMap_predAbove m i).comp (ih θ)

instance functor_isFibered_simplexMap {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) :
    (monotone_simplexMap.{u} f).functor.IsFibered := by
  induction m generalizing n with
  | zero =>
    have hf : Function.Injective f := fun a b _ => Subsingleton.elim (α := Fin 1) a b
    exact (isLocalEmbedding_of_isInclusion (simplex.mapOfInjective.{u} f hf)).functor_isFibered
  | succ m ih =>
    by_cases hf : Function.Injective f
    · exact (isLocalEmbedding_of_isInclusion (simplex.mapOfInjective.{u} f hf)).functor_isFibered
    · obtain ⟨i, θ, hmap⟩ := exists_simplexMap_eq_comp f hf
      have := functor_isFibered_simplexMap_predAbove.{u} m i
      have := ih θ
      exact functor_isFibered_of_eq (Monotone.functor_isFibered_comp
        (monotone_simplexMap.{u} (Fin.predAboveOrderHom i)) (monotone_simplexMap.{u} θ)) _
        hmap.symm

def simplexOneToGlobeOne : simplex.{u} 1 → globe.{u} 1
  | ⟨(⊥, _), _⟩ => .pole true
  | ⟨(some _, ⊥), _⟩ => .pole false
  | ⟨(some _, some _), _⟩ => .susp ⊤

def globeOneToSimplexOne : globe.{u} 1 → simplex.{u} 1
  | .pole false => ⟨(some (⊤ : point.{u}), ⊥), fun h => WithBot.coe_ne_bot (congrArg Prod.fst h)⟩
  | .pole true => ⟨(⊥, some (⊤ : point.{u})), fun h => WithBot.coe_ne_bot (congrArg Prod.snd h)⟩
  | .susp _ => ⟨(some (⊤ : point.{u}), some (⊤ : point.{u})),
      fun h => WithBot.coe_ne_bot (congrArg Prod.fst h)⟩

def simplexOneOrderIsoGlobeOne : simplex.{u} 1 ≃o globe.{u} 1 where
  toFun := simplexOneToGlobeOne
  invFun := globeOneToSimplexOne
  left_inv p := by
    rcases p with ⟨⟨_ | ⟨⟩, _ | ⟨⟩⟩, h⟩
    · exact (h rfl).elim
    all_goals rfl
  right_inv p := by
    rcases p with (_ | _) | ⟨⟨⟩⟩ <;> rfl
  map_rel_iff' {p q} := by
    rcases p with ⟨⟨_ | ⟨⟩, _ | ⟨⟩⟩, h⟩ <;> rcases q with ⟨⟨_ | ⟨⟩, _ | ⟨⟩⟩, h'⟩
    all_goals first | exact (h rfl).elim | exact (h' rfl).elim | skip
    all_goals refine ⟨fun hh => ?_, fun hh => ?_⟩
    all_goals first
      | exact le_rfl
      | trivial
      | exact absurd hh (by decide)
      | exact ⟨bot_le, le_of_eq rfl⟩
      | exact ⟨le_of_eq rfl, bot_le⟩
      | exact ⟨le_of_eq rfl, le_of_eq rfl⟩
      | exact absurd hh.1 (WithBot.not_coe_le_bot _)
      | exact absurd hh.2 (WithBot.not_coe_le_bot _)

def simplexOneIsoGlobeOne : simplex.{u} 1 ≅ globe.{u} 1 :=
  isoMk simplexOneOrderIsoGlobeOne fun {x y} h => by
    rcases x with ⟨⟨_ | a, _ | b⟩, hx⟩ <;> rcases y with ⟨⟨_ | c, _ | d⟩, hy⟩
    all_goals first | exact (hx rfl).elim | exact (hy rfl).elim | skip
    all_goals first
      | exact absurd h.lt.le.1 (WithBot.not_coe_le_bot _)
      | exact absurd h.lt.le.2 (WithBot.not_coe_le_bot _)
      | exact absurd h.lt (lt_irrefl _)
      | skip
    · have hmem : (⟨(⊥, some d), hy⟩ : simplex.{u} 1) ∈
          (simplex.{u} 1).faces true ⟨(some a, some b), hx⟩ :=
        (mem_faces_join (P := point) (Q := simplex 0)).2 (mem_faces_grayProduct.2 (.inl
          ⟨bot_mem_faces_augmentation.2 ⟨isMin_point a, rfl⟩, rfl⟩))
      exact hmem.2.symm
    · have h1 : grade ℕ (((a : WithBot point.{u})) : augmentation point.{u}) = 1 := by
        have h0 : grade ℕ (⊥ : augmentation point.{u}) = 0 := grade_eq_zero_iff.2 isMin_bot
        have := Nat.covBy_iff_add_one_eq.1 ((WithBot.bot_covBy_coe.2 (isMin_point a) :
          (⊥ : augmentation point.{u}) ⋖ (a : WithBot point.{u})).grade ℕ)
        omega
      have hmem : (⟨(some c, ⊥), hy⟩ : simplex.{u} 1) ∈
          (simplex.{u} 1).faces false ⟨(some a, some b), hx⟩ :=
        (mem_faces_join (P := point) (Q := simplex 0)).2 (mem_faces_grayProduct.2 (.inr
          ⟨rfl, bot_mem_faces_augmentation.2 ⟨isMin_point (b : point.{u}), by
            change (grade ℕ (((a : WithBot point.{u})) : augmentation point.{u})).bodd ^^ false =
              true
            rw [h1]
            rfl⟩⟩))
      exact hmem.2.symm

theorem simplexOneIsoGlobeOne_simplexMap_δ (ε : Bool) (p : simplex.{u} 0) :
    simplexOneIsoGlobeOne.hom (simplexMap (SimplexCategory.δ (cond ε 0 1 : Fin 2)).toOrderHom p) =
      .pole ε := by
  have hp : simplexVertices 0 p = {0} := by
    obtain ⟨i, hi⟩ := simplexVertices_nonempty 0 p
    exact Finset.eq_singleton_iff_unique_mem.2
      ⟨Fin.fin_one_eq_zero i ▸ hi, fun j _ => Fin.fin_one_eq_zero j⟩
  have h : simplexMap (SimplexCategory.δ (cond ε 0 1 : Fin 2)).toOrderHom p =
      globeOneToSimplexOne (.pole ε) := by
    rw [simplexMap_eq_iff, hp]
    cases ε <;> decide
  rw [h]
  exact simplexOneOrderIsoGlobeOne.apply_symm_apply (.pole ε)

end Atoms.Molecule.OGP
