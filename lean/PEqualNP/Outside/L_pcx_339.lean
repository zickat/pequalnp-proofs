import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_339_aux

section enum
variable {n : ℕ}

open Classical in
noncomputable def hdC (σ : Equiv.Perm (Fin n)) (y : Fin n) : Fin n :=
  (Finset.univ.filter (fun z => σ.SameCycle y z)).min'
    ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, Equiv.Perm.SameCycle.refl _ _⟩⟩

theorem hdC_mem (σ : Equiv.Perm (Fin n)) (y : Fin n) : σ.SameCycle y (hdC σ y) := by
  classical
  have := Finset.min'_mem (Finset.univ.filter (fun z => σ.SameCycle y z))
    ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, Equiv.Perm.SameCycle.refl _ _⟩⟩
  unfold hdC
  convert (Finset.mem_filter.1 this).2

theorem hdC_congr (σ : Equiv.Perm (Fin n)) {y y' : Fin n} (h : σ.SameCycle y y') :
    hdC σ y = hdC σ y' := by
  unfold hdC
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

theorem hdC_apply (σ : Equiv.Perm (Fin n)) (y : Fin n) : hdC σ (σ y) = hdC σ y :=
  hdC_congr σ (Equiv.Perm.sameCycle_apply_left.2 (Equiv.Perm.SameCycle.refl σ y))

theorem hdC_idem (σ : Equiv.Perm (Fin n)) (y : Fin n) : hdC σ (hdC σ y) = hdC σ y :=
  hdC_congr σ (hdC_mem σ y).symm

theorem kk_exists (σ : Equiv.Perm (Fin n)) (y : Fin n) : ∃ i, (σ ^ i) (hdC σ y) = y := by
  obtain ⟨i, -, hi⟩ := (hdC_mem σ y).symm.exists_pow_eq'
  exact ⟨i, hi⟩

open Classical in
noncomputable def kk (σ : Equiv.Perm (Fin n)) (y : Fin n) : ℕ := Nat.find (kk_exists σ y)

theorem kk_spec (σ : Equiv.Perm (Fin n)) (y : Fin n) : (σ ^ (kk σ y)) (hdC σ y) = y := by
  classical
  unfold kk; convert Nat.find_spec (kk_exists σ y)

theorem kk_min (σ : Equiv.Perm (Fin n)) (y : Fin n) {i : ℕ} (h : (σ ^ i) (hdC σ y) = y) :
    kk σ y ≤ i := by
  classical
  unfold kk; convert Nat.find_min' (kk_exists σ y) h

theorem kk_lt (σ : Equiv.Perm (Fin n)) (y : Fin n) : kk σ y < orderOf σ := by
  obtain ⟨i, hi, h⟩ := (hdC_mem σ y).symm.exists_pow_eq'
  exact lt_of_le_of_lt (kk_min σ y h) hi

theorem kk_zero (σ : Equiv.Perm (Fin n)) (y : Fin n) (h : hdC σ y = y) : kk σ y = 0 := by
  have := kk_min σ y (i := 0) (by simpa using h)
  omega

theorem kk_succ (σ : Equiv.Perm (Fin n)) (y : Fin n) (h : σ y ≠ hdC σ y) :
    kk σ (σ y) = kk σ y + 1 := by
  apply le_antisymm
  · apply kk_min
    rw [hdC_apply, pow_succ', Equiv.Perm.mul_apply, kk_spec]
  · have hs := kk_spec σ (σ y)
    rw [hdC_apply] at hs
    rcases hj : kk σ (σ y) with _ | j
    · rw [hj, pow_zero, Equiv.Perm.one_apply] at hs
      exact absurd hs.symm h
    · rw [hj, pow_succ', Equiv.Perm.mul_apply] at hs
      have := kk_min σ y (σ.injective hs)
      omega

noncomputable def key (σ : Equiv.Perm (Fin n)) (y : Fin n) : ℕ :=
  orderOf σ * (hdC σ y).val + kk σ y

theorem key_inj (σ : Equiv.Perm (Fin n)) : Function.Injective (key σ) := by
  intro y y' h
  have hN : 0 < orderOf σ := orderOf_pos σ
  have h1 := kk_lt σ y
  have h2 := kk_lt σ y'
  unfold key at h
  have ha : (hdC σ y).val = (hdC σ y').val := by
    have e1 : (orderOf σ * (hdC σ y).val + kk σ y) / orderOf σ = (hdC σ y).val := by
      rw [Nat.mul_add_div hN, Nat.div_eq_of_lt h1, add_zero]
    have e2 : (orderOf σ * (hdC σ y').val + kk σ y') / orderOf σ = (hdC σ y').val := by
      rw [Nat.mul_add_div hN, Nat.div_eq_of_lt h2, add_zero]
    rw [← e1, ← e2, h]
  have hb : kk σ y = kk σ y' := by rw [ha] at h; omega
  have hh : hdC σ y = hdC σ y' := Fin.ext ha
  rw [← kk_spec σ y, ← kk_spec σ y', hb, hh]

theorem key_apply (σ : Equiv.Perm (Fin n)) (y : Fin n) (h : σ y ≠ hdC σ y) :
    key σ (σ y) = key σ y + 1 := by
  unfold key; rw [hdC_apply, kk_succ σ y h]; ring

theorem exists_enum (σ : Equiv.Perm (Fin n)) : ∃ e : Fin n ≃ Fin n,
    (∀ k (hk : k + 1 < n), hdC σ (e ⟨k+1, hk⟩) ≠ e ⟨k+1, hk⟩ →
      σ (e ⟨k, by omega⟩) = e ⟨k+1, hk⟩) ∧
    (∀ (h : 0 < n), hdC σ (e ⟨0, h⟩) = e ⟨0, h⟩) ∧
    (∀ k (hk : k < n), k + 1 = n → σ (e ⟨k, hk⟩) = hdC σ (e ⟨k, hk⟩)) ∧
    (∀ k (hk : k + 1 < n), hdC σ (e ⟨k+1, hk⟩) = e ⟨k+1, hk⟩ →
      σ (e ⟨k, by omega⟩) = hdC σ (e ⟨k, by omega⟩)) := by
  classical
  set K := Finset.univ.image (key σ) with hKdef
  have hK : K.card = n := by
    rw [Finset.card_image_of_injective _ (key_inj σ), Finset.card_univ, Fintype.card_fin]
  set f := K.orderEmbOfFin hK with hf
  have hmemK : ∀ y, key σ y ∈ K := fun y => Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hK2 : ∀ a ∈ K, ∃ u, f u = a := by
    intro a ha
    have : a ∈ Set.range f := by rw [hf, Finset.range_orderEmbOfFin]; exact ha
    exact this
  have hex : ∀ t, ∃ y, key σ y = f t := fun t => by
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 (K.orderEmbOfFin_mem hK t)
    exact ⟨y, hy⟩
  choose g hg using hex
  have ginj : Function.Injective g := by
    intro a b h
    have := congrArg (key σ) h
    rw [hg, hg] at this
    exact f.injective this
  let e := Equiv.ofBijective g (Finite.injective_iff_bijective.1 ginj)
  have he : ∀ t, key σ (e t) = f t := hg
  have hlt : ∀ a b, f a < f b ↔ a < b := fun a b => f.lt_iff_lt
  have hle : ∀ a b, f a ≤ f b ↔ a ≤ b := fun a b => f.le_iff_le

  have pred : ∀ t, hdC σ (e t) ≠ e t →
      ∃ u, f u + 1 = f t ∧ σ (e u) = e t := by
    intro t ht
    set z := σ.symm (e t)
    have hz : σ z = e t := by simp [z]
    have hz2 : σ z ≠ hdC σ z := by
      rw [hz]; intro h; apply ht; rw [← hz, hdC_apply, hz]; exact h.symm
    obtain ⟨u, hu⟩ := hK2 _ (hmemK z)
    refine ⟨u, ?_, ?_⟩
    · rw [hu, ← he, ← hz, key_apply σ z hz2]
    · have : e u = z := by apply key_inj σ; rw [he, hu]
      rw [this, hz]
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro k hk ht
    obtain ⟨u, hu1, hu2⟩ := pred _ ht
    have h1 : u < ⟨k+1, hk⟩ := (hlt _ _).1 (by omega)
    have h2 : (⟨k, by omega⟩ : Fin n) < ⟨k+1, hk⟩ := by simp [Fin.lt_def]
    have h3 := (hlt _ _).2 h2
    have h4 : u ≤ ⟨k, by omega⟩ := by rw [Fin.le_def]; rw [Fin.lt_def] at h1; simp at h1 ⊢; omega
    have h5 := (hle _ _).2 h4
    have h6 : f u = f ⟨k, by omega⟩ := by omega
    rw [← f.injective h6]; exact hu2
  · intro h
    by_contra ht
    obtain ⟨u, hu1, -⟩ := pred _ ht
    have h1 : u < ⟨0, h⟩ := (hlt _ _).1 (by omega)
    rw [Fin.lt_def] at h1; simp at h1
  · intro k hk hkn
    by_contra ht
    have h1 := key_apply σ _ ht
    obtain ⟨u, hu⟩ := hK2 _ (hmemK (σ (e ⟨k, hk⟩)))
    rw [he] at h1
    have h2 : (⟨k, hk⟩ : Fin n) < u := (hlt _ _).1 (by omega)
    rw [Fin.lt_def] at h2; simp at h2; omega
  · intro k hk ht
    by_contra hw
    set w := e ⟨k, by omega⟩ with hwdef
    have h1 := key_apply σ _ hw
    obtain ⟨u, hu⟩ := hK2 _ (hmemK (σ w))
    have hws : key σ w = f ⟨k, by omega⟩ := he _
    have h2 : (⟨k, by omega⟩ : Fin n) < u := (hlt _ _).1 (by omega)
    have h3 : (⟨k+1, hk⟩ : Fin n) ≤ u := by
      rw [Fin.le_def]; rw [Fin.lt_def] at h2; simp at h2 ⊢; omega
    have h4 := (hle _ _).2 h3
    have hks : f ⟨k, by omega⟩ < f ⟨k+1, hk⟩ := (hlt _ _).2 (by simp [Fin.lt_def])
    have hkt : key σ (e ⟨k+1, hk⟩) = orderOf σ * (e ⟨k+1, hk⟩).val := by
      unfold key; rw [kk_zero σ _ ht, ht, add_zero]
    have hkw : key σ w = orderOf σ * (hdC σ w).val + kk σ w := rfl
    have hkwlt := kk_lt σ w
    have hlt1 : (hdC σ w).val < (e ⟨k+1, hk⟩).val := by
      have : orderOf σ * (hdC σ w).val < orderOf σ * (e ⟨k+1, hk⟩).val := by
        have A : key σ w < key σ (e ⟨k+1,hk⟩) := by rw [hws, he]; exact hks
        rw [← hkt]; rw [hkw] at A; omega
      exact Nat.lt_of_mul_lt_mul_left this
    have hm : orderOf σ * ((hdC σ w).val + 1) ≤ orderOf σ * (e ⟨k+1, hk⟩).val :=
      Nat.mul_le_mul_left _ hlt1
    have heq : key σ (σ w) = key σ (e ⟨k+1, hk⟩) := by
      have A : key σ (e ⟨k+1,hk⟩) ≤ key σ (σ w) := by rw [he, ← hu]; exact h4
      rw [mul_add, mul_one] at hm
      rw [h1, hkw] at A ⊢
      rw [hkt] at A ⊢
      omega
    have := key_inj σ heq
    apply hw
    rw [this, ← ht, ← this, hdC_apply]

end enum

section stream
variable {n : ℕ}

noncomputable def dcount {n : ℕ} (x : Bool × Fin n → Bool) (P : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,P i))).card

noncomputable def stepT (σ : Equiv.Perm (Fin n)) (e : Fin n ≃ Fin n)
    (t p : ℕ) (s : Bool × Bool × ZMod (n+1) × ZMod (n+1)) (bit : Bool) :
    Bool × Bool × ZMod (n+1) × ZMod (n+1) :=
  if h : t < n then
    if p = 0 then
      (if hdC σ (e ⟨t,h⟩) = e ⟨t,h⟩ then (bit, bit, s.2.2.1, s.2.2.2)
       else (s.1, bit, s.2.2.1, s.2.2.2 + (if bit ≠ s.2.1 then 1 else 0)))
    else
      (s.1, bit, s.2.2.1 + (if s.2.1 ≠ bit then 1 else 0),
        s.2.2.2 + (if σ (e ⟨t,h⟩) = hdC σ (e ⟨t,h⟩) then (if s.1 ≠ bit then 1 else 0) else 0))
  else s

noncomputable def readT (P : Equiv.Perm (Fin n)) (e : Fin n ≃ Fin n) (x : Bool × Fin n → Bool)
    (t p : ℕ) : Bool :=
  if h : t < n then (if p = 0 then x (false, e ⟨t,h⟩) else x (true, P (e ⟨t,h⟩))) else false

noncomputable def gP (P : Equiv.Perm (Fin n)) (e : Fin n ≃ Fin n) (x : Bool × Fin n → Bool)
    (t : ℕ) : ℕ :=
  if h : t < n then (if x (false, e ⟨t,h⟩) ≠ x (true, P (e ⟨t,h⟩)) then 1 else 0) else 0

noncomputable def gQ (Q : Equiv.Perm (Fin n)) (x : Bool × Fin n → Bool) (y : Fin n) : ℕ :=
  if x (false, y) ≠ x (true, Q y) then 1 else 0

noncomputable def gQn (Q : Equiv.Perm (Fin n)) (e : Fin n ≃ Fin n) (x : Bool × Fin n → Bool)
    (t : ℕ) : ℕ :=
  if h : t < n then gQ Q x (e ⟨t,h⟩) else 0

def Inv (P Q σ : Equiv.Perm (Fin n)) (e : Fin n ≃ Fin n) (x : Bool × Fin n → Bool) (m : ℕ)
    (s : Bool × Bool × ZMod (n+1) × ZMod (n+1)) : Prop :=
  s.2.2.1 = (Nat.cast (∑ j ∈ Finset.range m, gP P e x j) : ZMod (n+1)) ∧ (m = 0 → s.2.2.2 = 0) ∧
  ∀ k (hk : k < n), k + 1 = m →
    s.1 = x (false, hdC σ (e ⟨k,hk⟩)) ∧ s.2.1 = x (true, P (e ⟨k,hk⟩)) ∧
    s.2.2.2 + (Nat.cast (if σ (e ⟨k,hk⟩) = hdC σ (e ⟨k,hk⟩) then 0 else gQ Q x (hdC σ (e ⟨k,hk⟩)))
      : ZMod (n+1)) = (Nat.cast (∑ j ∈ Finset.range m, gQn Q e x j) : ZMod (n+1))

theorem gQ_cast (Q : Equiv.Perm (Fin n)) (x : Bool × Fin n → Bool) (y : Fin n) (c : Bool)
    (hc : c = x (true, Q y)) :
    (if x (false, y) ≠ c then (1 : ZMod (n+1)) else 0) = (Nat.cast (gQ Q x y) : ZMod (n+1)) := by
  subst hc; unfold gQ; split_ifs <;> simp

theorem inv_step (P Q σ : Equiv.Perm (Fin n)) (hQσ : ∀ y, Q (σ y) = P y) (e : Fin n ≃ Fin n)
    (hP1 : ∀ k (hk : k + 1 < n), hdC σ (e ⟨k+1, hk⟩) ≠ e ⟨k+1, hk⟩ →
      σ (e ⟨k, by omega⟩) = e ⟨k+1, hk⟩)
    (hP2 : ∀ (h : 0 < n), hdC σ (e ⟨0, h⟩) = e ⟨0, h⟩)
    (hP6 : ∀ k (hk : k + 1 < n), hdC σ (e ⟨k+1, hk⟩) = e ⟨k+1, hk⟩ →
      σ (e ⟨k, by omega⟩) = hdC σ (e ⟨k, by omega⟩))
    (x : Bool × Fin n → Bool) (m : ℕ) (hm : m < n) (s : Bool × Bool × ZMod (n+1) × ZMod (n+1))
    (hI : Inv P Q σ e x m s) :
    Inv P Q σ e x (m+1) (stepT σ e m 1 (stepT σ e m 0 s (x (false, e ⟨m,hm⟩)))
      (x (true, P (e ⟨m,hm⟩)))) := by
  obtain ⟨hcP, hz, hlast⟩ := hI
  have hs0 : ∀ s' : Bool × Bool × ZMod (n+1) × ZMod (n+1), ∀ bit, stepT σ e m 0 s' bit =
      if hdC σ (e ⟨m,hm⟩) = e ⟨m,hm⟩ then (bit, bit, s'.2.2.1, s'.2.2.2)
       else (s'.1, bit, s'.2.2.1, s'.2.2.2 + (if bit ≠ s'.2.1 then 1 else 0)) := by
    intro s' bit; simp [stepT, hm]
  have hs1 : ∀ s' : Bool × Bool × ZMod (n+1) × ZMod (n+1), ∀ bit, stepT σ e m 1 s' bit =
      (s'.1, bit, s'.2.2.1 + (if s'.2.1 ≠ bit then 1 else 0),
        s'.2.2.2 + (if σ (e ⟨m,hm⟩) = hdC σ (e ⟨m,hm⟩) then (if s'.1 ≠ bit then 1 else 0) else 0)) := by
    intro s' bit; simp [stepT, hm]
  have hgP : gP P e x m = if x (false, e ⟨m,hm⟩) ≠ x (true, P (e ⟨m,hm⟩)) then 1 else 0 := by
    simp [gP, hm]
  have hgQ : gQn Q e x m = gQ Q x (e ⟨m,hm⟩) := by simp [gQn, hm]
  set y := e ⟨m,hm⟩ with hy
  have hcPgoal : ∀ s' : Bool × Bool × ZMod (n+1) × ZMod (n+1), s'.2.2.1 = s.2.2.1 →
      s'.2.1 = x (false, y) →
      (stepT σ e m 1 s' (x (true, P y))).2.2.1 =
        (Nat.cast (∑ j ∈ Finset.range (m+1), gP P e x j) : ZMod (n+1)) := by
    intro s' h1 h2
    rw [hs1, Finset.sum_range_succ, hgP]
    simp only [h1, h2, hcP]
    push_cast
    split_ifs <;> simp
  by_cases hst : hdC σ y = y
  ·
    have hpend : s.2.2.2 = (Nat.cast (∑ j ∈ Finset.range m, gQn Q e x j) : ZMod (n+1)) := by
      rcases m with _ | k
      · simp [hz rfl]
      · have h6 := hP6 k hm hst
        obtain ⟨-, -, h3⟩ := hlast k (by omega) rfl
        rw [if_pos h6] at h3
        simpa using h3
    rw [hs0, if_pos hst]
    refine ⟨hcPgoal _ rfl rfl, by omega, ?_⟩
    intro k hk hkm
    have ek : (⟨k,hk⟩ : Fin n) = ⟨m,hm⟩ := Fin.ext (by simp; omega)
    rw [ek, ← hy, hs1]
    refine ⟨by simp [hst], rfl, ?_⟩
    simp only
    rw [Finset.sum_range_succ, hgQ, hpend]
    by_cases hend : σ y = hdC σ y
    · rw [if_pos hend, if_pos hend]
      rw [gQ_cast Q x y _ (by rw [← hQσ, hend, hst])]
      push_cast
      ring
    · rw [if_neg hend, if_neg hend, hst]
      push_cast
      ring
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl; exact hst (hP2 hm)
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have h1 := hP1 k hm hst
    rw [← hy] at h1
    obtain ⟨hf, hl, hq⟩ := hlast k (by omega) rfl
    have hhd : hdC σ y = hdC σ (e ⟨k, by omega⟩) := by rw [← h1, hdC_apply]
    have hwend : σ (e ⟨k, by omega⟩) ≠ hdC σ (e ⟨k, by omega⟩) := by
      intro h; apply hst; rw [hhd, ← h, h1]
    have hlast' : s.2.1 = x (true, Q y) := by rw [hl, ← hQσ, h1]
    rw [hs0, if_neg hst]
    refine ⟨hcPgoal _ rfl rfl, by omega, ?_⟩
    intro k' hk' hkm
    have ek : (⟨k',hk'⟩ : Fin n) = ⟨k+1,hm⟩ := Fin.ext (by simp; omega)
    rw [ek, ← hy, hs1]
    refine ⟨by simp only; rw [hhd]; exact hf, rfl, ?_⟩
    simp only
    rw [Finset.sum_range_succ, hgQ, Nat.cast_add, ← hq, if_neg hwend, ← hhd,
      gQ_cast Q x y _ hlast']
    by_cases hend : σ y = hdC σ y
    · rw [if_pos hend, if_pos hend, hf, ← hhd]
      rw [gQ_cast Q x (hdC σ y) _ (by rw [← hQσ, hend])]
      push_cast
      ring
    · rw [if_neg hend, if_neg hend]
      push_cast
      ring

theorem foldl_finRange_range {α : Type} (m : ℕ) (g : ℕ → α → α) (s0 : α) :
    (List.finRange m).foldl (fun s k => g k.val s) s0 = (List.range m).foldl (fun s j => g j s) s0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_map, List.range_succ,
      List.foldl_append]
    simp only [Fin.coe_castSucc]
    rw [ih]; rfl

theorem foldl_conj {α β γ : Type} (enc : α ≃ γ) (F : β → α → α) (l : List β) (s0 : α) :
    l.foldl (fun st k => enc (F k (enc.symm st))) (enc s0) = enc (l.foldl (fun s k => F k s) s0) := by
  induction l generalizing s0 with
  | nil => rfl
  | cons a l ih => simp only [List.foldl_cons, Equiv.symm_apply_apply]; exact ih _

noncomputable def Gs (P σ : Equiv.Perm (Fin n)) (e : Fin n ≃ Fin n) (x : Bool × Fin n → Bool)
    (j : ℕ) (s : Bool × Bool × ZMod (n+1) × ZMod (n+1)) : Bool × Bool × ZMod (n+1) × ZMod (n+1) :=
  stepT σ e (j/2) (j%2) s (readT P e x (j/2) (j%2))

theorem rounds_succ (P σ : Equiv.Perm (Fin n)) (e : Fin n ≃ Fin n) (x : Bool × Fin n → Bool)
    (s0 : Bool × Bool × ZMod (n+1) × ZMod (n+1)) (m : ℕ) (hm : m < n) :
    (List.range (2*(m+1))).foldl (fun s j => Gs P σ e x j s) s0 =
      stepT σ e m 1 (stepT σ e m 0 ((List.range (2*m)).foldl (fun s j => Gs P σ e x j s) s0)
        (x (false, e ⟨m,hm⟩))) (x (true, P (e ⟨m,hm⟩))) := by
  rw [show 2*(m+1) = 2*m+1+1 by ring, List.range_succ, List.range_succ, List.foldl_append,
    List.foldl_append]
  have h1 : 2*m/2 = m := by omega
  have h2 : 2*m%2 = 0 := by omega
  have h3 : (2*m+1)/2 = m := by omega
  have h4 : (2*m+1)%2 = 1 := by omega
  simp only [List.foldl_cons, List.foldl_nil, Gs, h1, h2, h3, h4]
  simp [readT, hm]

theorem sum_gP (P : Equiv.Perm (Fin n)) (e : Fin n ≃ Fin n) (x : Bool × Fin n → Bool) :
    ∑ j ∈ Finset.range n, gP P e x j = dcount x P := by
  rw [← Fin.sum_univ_eq_sum_range]
  have : ∀ i : Fin n, gP P e x i =
      (fun y => if x (false,y) ≠ x (true, P y) then 1 else 0) (e i) := by
    intro i; simp [gP, i.2]
  simp_rw [this]
  rw [Equiv.sum_comp e (fun y => if x (false,y) ≠ x (true, P y) then 1 else 0)]
  unfold dcount; rw [Finset.card_filter]

theorem sum_gQ (Q : Equiv.Perm (Fin n)) (e : Fin n ≃ Fin n) (x : Bool × Fin n → Bool) :
    ∑ j ∈ Finset.range n, gQn Q e x j = dcount x Q := by
  rw [← Fin.sum_univ_eq_sum_range]
  have : ∀ i : Fin n, gQn Q e x i = gQ Q x (e i) := by
    intro i; simp [gQn, i.2]
  simp_rw [this]
  rw [Equiv.sum_comp e (gQ Q x)]
  unfold dcount gQ; rw [Finset.card_filter]

theorem dcount_le (x : Bool × Fin n → Bool) (P : Equiv.Perm (Fin n)) : dcount x P < n + 1 := by
  unfold dcount
  have := Finset.card_filter_le (Finset.univ : Finset (Fin n))
    (fun i : Fin n => x (false,i) ≠ x (true,P i))
  simp only [Finset.card_univ, Fintype.card_fin] at this
  omega

noncomputable def ordF (P : Equiv.Perm (Fin n)) (e : Fin n ≃ Fin n) (k : Fin (2*n)) : Bool × Fin n :=
  if k.val % 2 = 0 then (false, e ⟨k.val/2, by omega⟩) else (true, P (e ⟨k.val/2, by omega⟩))

theorem ordF_bij (P : Equiv.Perm (Fin n)) (e : Fin n ≃ Fin n) : Function.Bijective (ordF P e) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  intro a b h
  unfold ordF at h
  split_ifs at h with ha hb hb
  · simp only [Prod.mk.injEq, true_and, EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  · simp at h
  · simp at h
  · simp only [Prod.mk.injEq, true_and, EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq] at h
    exact Fin.ext (by omega)

theorem ordF_read (P : Equiv.Perm (Fin n)) (e : Fin n ≃ Fin n) (x : Bool × Fin n → Bool)
    (k : Fin (2*n)) : x (ordF P e k) = readT P e x (k.val/2) (k.val % 2) := by
  have hk : k.val / 2 < n := by omega
  unfold ordF readT
  rw [dif_pos hk]
  split_ifs <;> rfl

end stream

theorem stream (n : ℕ) (P Q : Equiv.Perm (Fin n)) :
    ∃ (order : Fin (2*n) ≃ Bool × Fin n) (init : Fin (4*(n+1)^2))
      (step : Fin (2*n) → Fin (4*(n+1)^2) → Bool → Fin (4*(n+1)^2))
      (outP outQ : Fin (4*(n+1)^2) → ℕ), ∀ x : Bool × Fin n → Bool,
      outP ((List.finRange (2*n)).foldl (fun st k => step k st (x (order k))) init) = dcount x P ∧
      outQ ((List.finRange (2*n)).foldl (fun st k => step k st (x (order k))) init) = dcount x Q := by
  classical
  set σ : Equiv.Perm (Fin n) := Q⁻¹ * P with hσ
  have hQσ : ∀ y, Q (σ y) = P y := by intro y; simp [hσ, Equiv.Perm.mul_apply]
  obtain ⟨e, hP1, hP2, hP5, hP6⟩ := exists_enum σ
  let enc : (Bool × Bool × ZMod (n+1) × ZMod (n+1)) ≃ Fin (4*(n+1)^2) :=
    Fintype.equivFinOfCardEq (by simp [ZMod.card]; ring)
  refine ⟨Equiv.ofBijective (ordF P e) (ordF_bij P e), enc (false,false,0,0),
    fun k st b => enc (stepT σ e (k.val/2) (k.val % 2) (enc.symm st) b),
    fun st => (enc.symm st).2.2.1.val, fun st => (enc.symm st).2.2.2.val, ?_⟩
  intro x
  have hF : ∀ (k : Fin (2*n)) (s : Bool × Bool × ZMod (n+1) × ZMod (n+1)),
      stepT σ e (k.val/2) (k.val % 2) s (x (Equiv.ofBijective (ordF P e) (ordF_bij P e) k)) =
        Gs P σ e x k.val s := by
    intro k s; simp only [Equiv.ofBijective_apply, ordF_read, Gs]
  have hfold : (List.finRange (2*n)).foldl (fun st k =>
      enc (stepT σ e (k.val/2) (k.val % 2) (enc.symm st)
        (x (Equiv.ofBijective (ordF P e) (ordF_bij P e) k)))) (enc (false,false,0,0)) =
      enc ((List.range (2*n)).foldl (fun s j => Gs P σ e x j s) (false,false,0,0)) := by
    simp only [hF]
    exact (foldl_conj enc (fun (k : Fin (2*n)) s => Gs P σ e x k.val s) _ _).trans
      (congrArg enc (foldl_finRange_range (2*n) (fun j s => Gs P σ e x j s) _))
  have hinv : ∀ m ≤ n, Inv P Q σ e x m
      ((List.range (2*m)).foldl (fun s j => Gs P σ e x j s) (false,false,0,0)) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨by simp, fun _ => rfl, fun k _ hk => by omega⟩
    | succ m ih =>
      intro hm
      rw [rounds_succ P σ e x _ m (by omega)]
      exact inv_step P Q σ hQσ e hP1 hP2 hP6 x m (by omega) _ (ih (by omega))
  obtain ⟨hcP, hz, hlast⟩ := hinv n le_rfl
  rw [hfold]
  simp only [Equiv.symm_apply_apply]
  refine ⟨?_, ?_⟩
  · rw [hcP, ZMod.val_natCast, sum_gP, Nat.mod_eq_of_lt (dcount_le x P)]
  · rcases n with _ | k
    · rw [hz rfl]; simp [dcount]
    · obtain ⟨-, -, h3⟩ := hlast k (by omega) rfl
      rw [if_pos (hP5 k (by omega) rfl)] at h3
      simp only [Nat.cast_zero, add_zero] at h3
      rw [h3, ZMod.val_natCast, sum_gQ, Nat.mod_eq_of_lt (dcount_le x Q)]

section dir2part

open Finset

def sg {n : ℕ} (b : Fin n → Bool) (i : Fin n) : ℤ := if b i then -1 else 1

theorem flip_sum {n : ℕ} (a : Fin n) (F : (Fin n → Bool) → ℤ)
    (hF : ∀ b, F (Function.update b a (!b a)) = F b) :
    ∑ b, sg b a * F b = 0 := by
  have hinv : Function.Involutive (fun b : Fin n → Bool => Function.update b a (!b a)) := by
    intro b; funext i
    by_cases h : i = a
    · subst h; simp
    · simp [Function.update_apply, h]
  have := Equiv.sum_comp hinv.toPerm (fun b => sg b a * F b)
  have h2 : ∀ b, sg (Function.update b a (!b a)) a * F (Function.update b a (!b a))
      = -(sg b a * F b) := by
    intro b; rw [hF]; simp only [sg, Function.update_self]; cases b a <;> simp
  simp only [Function.Involutive.coe_toPerm, h2, Finset.sum_neg_distrib] at this
  linarith

theorem sg_update {n : ℕ} (b : Fin n → Bool) (a i : Fin n) (h : i ≠ a) :
    sg (Function.update b a (!b a)) i = sg b i := by
  simp [sg, Function.update_apply, h]

def tt {n : ℕ} (π : Equiv.Perm (Fin n)) (b : Fin n → Bool) (i : Fin n) : ℤ :=
  if π i = i then 0 else sg b i * sg b (π i)

theorem sg_sq {n : ℕ} (b : Fin n → Bool) (i : Fin n) : sg b i * sg b i = 1 := by
  unfold sg; split_ifs <;> norm_num

theorem tt_abs {n : ℕ} (π : Equiv.Perm (Fin n)) (b : Fin n → Bool) (i i' : Fin n) :
    tt π b i * tt π b i' ≤ 1 := by
  unfold tt sg; split_ifs <;> norm_num

theorem pair_sum {n : ℕ} (π : Equiv.Perm (Fin n)) (i i' : Fin n) :
    ∑ b, tt π b i * tt π b i' ≤ if (i' = i ∨ i' = π i) then (2:ℤ)^n else 0 := by
  by_cases hi : π i = i
  · have : ∀ b, tt π b i * tt π b i' = 0 := by intro b; simp [tt, hi]
    simp only [this, Finset.sum_const_zero]; split_ifs <;> positivity
  by_cases hi' : π i' = i'
  · have : ∀ b, tt π b i * tt π b i' = 0 := by intro b; simp [tt, hi']
    simp only [this, Finset.sum_const_zero]; split_ifs <;> positivity
  by_cases hc : i' = i ∨ i' = π i
  · rw [if_pos hc]
    calc ∑ b, tt π b i * tt π b i' ≤ ∑ _b : Fin n → Bool, (1:ℤ) :=
          Finset.sum_le_sum (fun b _ => tt_abs π b i i')
      _ = 2^n := by simp
  rw [if_neg hc]
  push_neg at hc
  apply le_of_eq
  by_cases hA : i ≠ i' ∧ i ≠ π i'
  · have e : ∀ b, tt π b i * tt π b i' = sg b i * (sg b (π i) * sg b i' * sg b (π i')) := by
      intro b; simp only [tt, if_neg hi, if_neg hi']; ring
    simp only [e]
    apply flip_sum
    intro b
    rw [sg_update _ _ _ (Ne.symm (by intro h; exact hi h.symm |>.elim)),
      sg_update _ _ _ (Ne.symm hA.1), sg_update _ _ _ (Ne.symm hA.2)]
  · have hii : i = π i' := by
      push_neg at hA
      exact hA (fun h => hc.1 h.symm)
    have n1 : π i ≠ i' := fun h => hc.2 h.symm
    have n2 : π i ≠ π i' := fun h => hc.1 (π.injective h).symm
    have e : ∀ b, tt π b i * tt π b i' = sg b (π i) * (sg b i * sg b i' * sg b (π i')) := by
      intro b; simp only [tt, if_neg hi, if_neg hi']; ring
    simp only [e]
    apply flip_sum
    intro b
    rw [sg_update _ _ _ (fun h => hi h.symm), sg_update _ _ _ (Ne.symm n1),
      sg_update _ _ _ (Ne.symm n2)]

def TT {n : ℕ} (π : Equiv.Perm (Fin n)) (b : Fin n → Bool) : ℤ := ∑ i, tt π b i

theorem var_bound {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ∑ b, (TT π b)^2 ≤ 2 * n * 2^n := by
  have h1 : ∑ b, (TT π b)^2 = ∑ i, ∑ i', ∑ b, tt π b i * tt π b i' := by
    simp only [TT, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
  rw [h1]
  calc ∑ i, ∑ i', ∑ b, tt π b i * tt π b i'
      ≤ ∑ i : Fin n, ∑ i' : Fin n, (if (i' = i ∨ i' = π i) then (2:ℤ)^n else 0) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun i' _ => pair_sum π i i'))
    _ ≤ ∑ _i : Fin n, 2 * (2:ℤ)^n := by
        apply Finset.sum_le_sum; intro i _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have : (Finset.univ.filter (fun i' => i' = i ∨ i' = π i)).card ≤ 2 := by
          calc _ ≤ ({i, π i} : Finset (Fin n)).card := by
                apply Finset.card_le_card; intro y; simp
            _ ≤ 2 := Finset.card_le_two
        have : ((Finset.univ.filter (fun i' => i' = i ∨ i' = π i)).card : ℤ) ≤ 2 := by
          exact_mod_cast this
        have : (0:ℤ) ≤ 2^n := by positivity
        nlinarith
    _ = 2 * n * 2^n := by simp; ring

theorem link {n : ℕ} (π : Equiv.Perm (Fin n)) (b : Fin n → Bool) :
    (n:ℤ) - 2 * ((Finset.univ.filter (fun i => b i ≠ b (π i))).card : ℤ)
      = ((Finset.univ.filter (fun i => π i = i)).card : ℤ) + TT π b := by
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter, TT, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  have hn : (n:ℤ) = ∑ _i : Fin n, (1:ℤ) := by simp
  rw [hn, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  by_cases h : π i = i
  · simp [tt, h]
  · simp only [tt, if_neg h, sg]
    cases b i <;> cases b (π i) <;> simp

theorem good_test {n D f : ℕ} {T : ℤ} (hlink : (n:ℤ) - 2 * D = f + T) (hf : 128 * f ≤ n)
    (hT : ¬ ((n:ℤ)^2 < 1024 * T^2)) : 16 * Nat.dist (2 * D) n ≤ n := by
  push_neg at hT
  have h1 : 32 * T ≤ n := by nlinarith
  have h2 : -(n:ℤ) ≤ 32 * T := by nlinarith
  have h3 : (128:ℤ) * f ≤ n := by exact_mod_cast hf
  unfold Nat.dist
  omega

theorem good_coloring (n r : ℕ) (hn : 2048 * r < n) (π : Fin r → Equiv.Perm (Fin n))
    (S : Finset (Fin r))
    (hfix : ∀ l ∈ S, 128 * (Finset.univ.filter (fun i => π l i = i)).card ≤ n) :
    ∃ b : Fin n → Bool, ∀ l ∈ S,
      16 * Nat.dist (2 * (Finset.univ.filter (fun i => b i ≠ b (π l i))).card) n ≤ n := by
  classical
  have hnpos : 0 < n := by omega

  let bad : Fin r → Finset (Fin n → Bool) :=
    fun l => Finset.univ.filter (fun b => (n:ℤ)^2 < 1024 * (TT (π l) b)^2)
  have hbad : ∀ l, ((bad l).card : ℤ) * n ≤ 2048 * 2^n := by
    intro l
    have hv := var_bound (π l)
    have : ((bad l).card : ℤ) * (n:ℤ)^2 ≤ ∑ b, 1024 * (TT (π l) b)^2 := by
      calc ((bad l).card : ℤ) * (n:ℤ)^2 = ∑ b ∈ bad l, (n:ℤ)^2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ b ∈ bad l, 1024 * (TT (π l) b)^2 := by
            apply Finset.sum_le_sum; intro b hb
            simp only [bad, Finset.mem_filter] at hb; exact hb.2.le
        _ ≤ ∑ b, 1024 * (TT (π l) b)^2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro _ _ _; positivity
    rw [← Finset.mul_sum] at this
    have hn' : (0:ℤ) < n := by exact_mod_cast hnpos
    have : ((bad l).card : ℤ) * n * n ≤ 2048 * 2^n * n := by nlinarith
    exact le_of_mul_le_mul_right this hn'
  have hunion : (Finset.univ.biUnion bad).card < 2^n := by
    have h1 := Finset.card_biUnion_le (s := Finset.univ) (t := bad)
    have h2 : (∑ l, ((bad l).card : ℤ)) * n ≤ r * (2048 * 2^n) := by
      rw [Finset.sum_mul]
      calc ∑ l, ((bad l).card : ℤ) * n ≤ ∑ _l : Fin r, (2048 * 2^n : ℤ) :=
            Finset.sum_le_sum (fun l _ => hbad l)
        _ = r * (2048 * 2^n) := by simp
    have h3 : ((Finset.univ.biUnion bad).card : ℤ) ≤ ∑ l, ((bad l).card : ℤ) := by
      exact_mod_cast h1
    have h4 : (2048 * r : ℤ) < n := by exact_mod_cast hn
    have h5 : (0:ℤ) < 2^n := by positivity
    have h6 : ((Finset.univ.biUnion bad).card : ℤ) * n < 2^n * n := by
      have h0 : (0:ℤ) ≤ n := by positivity
      nlinarith
    have hn' : (0:ℤ) < n := by exact_mod_cast hnpos
    have := lt_of_mul_lt_mul_right h6 hn'.le
    exact_mod_cast this
  have : ∃ b, b ∉ Finset.univ.biUnion bad := by
    by_contra hcon
    push_neg at hcon
    have : (Finset.univ : Finset (Fin n → Bool)) ⊆ Finset.univ.biUnion bad := fun b _ => hcon b
    have := Finset.card_le_card this
    simp at this
    omega
  obtain ⟨b, hb⟩ := this
  refine ⟨b, fun l hl => ?_⟩
  have hnb : b ∉ bad l := fun h => hb (Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, h⟩)
  simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hnb
  exact good_test (link (π l) b) (hfix l hl) hnb

noncomputable def tst {n : ℕ} (x : Bool × Fin n → Bool) (P : Equiv.Perm (Fin n)) : Bool :=
  decide (16 * Nat.dist (2 * dcount x P) n ≤ n)

theorem dir2 (n r d R u v : ℕ) (M : Fin r → Equiv.Perm (Fin n))
    (menu : Fin d → Fin r × Fin r) (hn : 8192*r < n)
    (hM : ∀ j l : Fin r, j ≠ l → 128*(univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n)
    (choose : Fin R → Fin d) (decode : Fin R → Bool → Bool → Bool)
    (ans : (Bool × Fin n → Bool) → Fin R → Bool)
    (H : ∀ x : Bool × Fin n → Bool,
      (∀ seed, ans x seed = decode seed (tst x (M (menu (choose seed)).1))
        (tst x (M (menu (choose seed)).2))) ∧
      ((∀ j, tst x (M j) = true) → (univ.filter (fun seed => ans x seed = false)).card ≤ u) ∧
      ((∃ j, tst x (M j) = false) → (univ.filter (fun seed => ans x seed = true)).card ≤ v)) :
    ∃ w : Fin d → ℕ, (∑ h, w h) = R - u ∧
      ∀ j : Fin r, (∑ h, if j = (menu h).1 ∨ j = (menu h).2 then 0 else w h) ≤ v := by
  classical

  let x0 : Bool × Fin n → Bool := fun p => !p.1 && decide (p.2.val < n / 2)
  have hx0 : ∀ j, tst x0 (M j) = true := by
    intro j
    have hjr := j.isLt
    have hc : dcount x0 (M j) = n / 2 := by
      unfold dcount
      have : (univ.filter (fun i : Fin n => x0 (false,i) ≠ x0 (true, M j i)))
          = univ.filter (fun i : Fin n => (i : ℕ) < n / 2) := by
        apply Finset.filter_congr; intro i _; simp [x0]
      rw [this, Fin.card_filter_val_lt]; omega
    unfold tst; rw [hc]; simp only [decide_eq_true_eq]; unfold Nat.dist; omega
  obtain ⟨H0a, H0b, -⟩ := H x0
  have hans0 : ∀ seed, ans x0 seed = decode seed true true := by
    intro seed; rw [H0a, hx0, hx0]
  have hfalse := H0b hx0
  let S0 := univ.filter (fun seed : Fin R => decode seed true true = true)
  have hS0 : R - u ≤ S0.card := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin R)))
      (fun seed => decode seed true true = true)
    have h2 : (univ.filter (fun seed : Fin R => ¬ decode seed true true = true))
        = univ.filter (fun seed => ans x0 seed = false) := by
      apply Finset.filter_congr; intro s _; rw [hans0]; simp
    rw [h2, Finset.card_univ, Fintype.card_fin] at h1
    have h3 : S0.card = (univ.filter fun seed : Fin R => decode seed true true = true).card := rfl
    omega
  obtain ⟨S, hSS0, hScard⟩ := Finset.exists_subset_card_eq hS0
  refine ⟨fun h => (S.filter (fun s => choose s = h)).card, ?_, ?_⟩
  · rw [← hScard]
    exact (Finset.card_eq_sum_card_fiberwise (f := choose) (t := univ) (by simp)).symm
  intro j

  let π : Fin r → Equiv.Perm (Fin n) := fun l => (M l).trans (M j).symm
  obtain ⟨b, hb⟩ := good_coloring n r (by omega) π (univ.erase j) (by
    intro l hl
    have hlj : l ≠ j := Finset.ne_of_mem_erase hl
    have : univ.filter (fun i => π l i = i) = univ.filter (fun i : Fin n => M l i = M j i) := by
      apply Finset.filter_congr; intro i _
      simp only [π, Equiv.trans_apply]
      exact Equiv.symm_apply_eq _
    rw [this]; exact hM l j hlj)
  let xj : Bool × Fin n → Bool := fun p => if p.1 then b ((M j).symm p.2) else b p.2
  have hxl : ∀ l, l ≠ j → tst xj (M l) = true := by
    intro l hl
    have := hb l (Finset.mem_erase.2 ⟨hl, Finset.mem_univ _⟩)
    have e : univ.filter (fun i => xj (false,i) ≠ xj (true, M l i))
        = univ.filter (fun i => b i ≠ b (π l i)) := by
      apply Finset.filter_congr; intro i _; simp [xj, π]
    unfold tst dcount; rw [e]; simp only [decide_eq_true_eq]; exact this
  have hxj : tst xj (M j) = false := by
    have hz : dcount xj (M j) = 0 := by
      unfold dcount; simp [xj]
    have hnpos : 0 < n := by omega
    unfold tst; rw [hz]; simp only [decide_eq_false_iff_not]; unfold Nat.dist; omega
  obtain ⟨Hja, -, Hjc⟩ := H xj
  have hv := Hjc ⟨j, hxj⟩
  let cond : Fin d → Prop := fun h => j = (menu h).1 ∨ j = (menu h).2
  let S' := S.filter (fun s => ¬ cond (choose s))
  have hterm : ∀ h, (if j = (menu h).1 ∨ j = (menu h).2 then 0
      else (S.filter (fun s => choose s = h)).card) = (S'.filter (fun s => choose s = h)).card := by
    intro h
    simp only [S', Finset.filter_filter]
    split_ifs with hc
    · symm; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro s _ ⟨h1, h2⟩; exact h1 (h2 ▸ hc)
    · congr 1; apply Finset.filter_congr; intro s _
      constructor
      · intro h2; exact ⟨h2 ▸ hc, h2⟩
      · intro h2; exact h2.2
  simp only [hterm]
  rw [← Finset.card_eq_sum_card_fiberwise (f := choose) (t := univ) (by simp)]
  refine le_trans (Finset.card_le_card ?_) hv
  intro s hs
  simp only [S', Finset.mem_filter, cond, not_or] at hs
  have hs0 := hSS0 hs.1
  simp only [S0, Finset.mem_filter] at hs0
  rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
  rw [Hja, hxl _ (Ne.symm hs.2.1), hxl _ (Ne.symm hs.2.2)]
  exact hs0.2

theorem fiber_le {d R K : ℕ} (w : Fin d → ℕ) (hK : ∑ h, w h = K) (h : Fin d) :
    (univ.filter (fun s : Fin R => ∃ hs : s.val < K,
      (finSigmaFinEquiv.symm (Fin.cast hK.symm ⟨s.val, hs⟩) : (i : Fin d) × Fin (w i)).1 = h)).card
      ≤ w h := by
  classical
  calc _ = ((univ.filter (fun s : Fin R => ∃ hs : s.val < K,
      (finSigmaFinEquiv.symm (Fin.cast hK.symm ⟨s.val, hs⟩) : (i : Fin d) × Fin (w i)).1 = h)).image
        (fun s : Fin R => s.val)).card :=
        (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ ((univ : Finset (Fin (w h))).image
          (fun q => ((finSigmaFinEquiv (⟨h, q⟩ : (i : Fin d) × Fin (w i)) : Fin _) : ℕ))).card := by
        apply Finset.card_le_card
        intro m hm
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
        obtain ⟨s, ⟨hs, hsh⟩, rfl⟩ := hm
        have key : ∀ p : (i : Fin d) × Fin (w i), p.1 = h →
            ∃ q : Fin (w h), finSigmaFinEquiv (⟨h, q⟩ : (i : Fin d) × Fin (w i))
              = finSigmaFinEquiv p := by
          rintro ⟨i, q⟩ rfl; exact ⟨q, rfl⟩
        obtain ⟨q, hq⟩ := key _ hsh
        refine ⟨q, ?_⟩
        rw [hq, Equiv.apply_symm_apply]; rfl
    _ ≤ w h := Finset.card_image_le.trans (by simp)

end dir2part

end PEqualNP.Outside.L_pcx_339_aux

open PEqualNP.Outside.L_pcx_339_aux in
theorem PEqualNP.Outside.L_pcx_339 : (∀ (n r d R u v : ℕ), 2 ≤ r → 0 < d → 0 < R → u ≤ R →
  ∀ (M : Fin r → Equiv.Perm (Fin n)) (menu : Fin d → Fin r × Fin r),
    let V := Bool × Fin n
    let X := V → Bool
    let test := fun (x : X) (j : Fin r) =>
      let D := (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M j i))).card
      decide (16 * Nat.dist (2*D) n ≤ n)
    let cap := 4*(n+1)^2
    let feasible := ∃ (choose : Fin R → Fin d) (decode : Fin R → Bool → Bool → Bool)
      (order : Fin d → (Fin (2*n) ≃ V)) (init : Fin R → Fin cap)
      (step : Fin R → Fin (2*n) → Fin cap → Bool → Fin cap) (out : Fin R → Fin cap → Bool),
      ∀ x : X,
        let answer := fun seed : Fin R => out seed ((List.finRange (2*n)).foldl
          (fun st k => step seed k st (x (order (choose seed) k))) (init seed))
        (∀ seed : Fin R, answer seed = decode seed (test x (menu (choose seed)).1)
          (test x (menu (choose seed)).2)) ∧
        ((∀ j : Fin r, test x j = true) →
          (Finset.univ.filter (fun seed : Fin R => answer seed = false)).card ≤ u) ∧
        ((∃ j : Fin r, test x j = false) →
          (Finset.univ.filter (fun seed : Fin R => answer seed = true)).card ≤ v)
    let weights := ∃ w : Fin d → ℕ, (∑ h : Fin d, w h) = R-u ∧
      ∀ j : Fin r, (∑ h : Fin d, if j = (menu h).1 ∨ j = (menu h).2 then 0 else w h) ≤ v
    (weights → feasible) ∧ (8192*r < n →
      (∀ j l : Fin r, j ≠ l →
        128*(Finset.univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n) →
      feasible → weights)) := by
  intro n r d R u v hr hd hR hu M menu
  dsimp only
  refine ⟨?_, ?_⟩
  · rintro ⟨w, hsum, hw⟩
    classical
    choose ord ini stp oP oQ hst using
      fun h : Fin d => stream n (M (menu h).1) (M (menu h).2)
    have hP := fun h x => (hst h x).1
    have hQ := fun h x => (hst h x).2
    let T : ℕ → Bool := fun D => decide (16 * Nat.dist (2*D) n ≤ n)
    let csel : Fin R → Fin d := fun s => if hs : s.val < R - u then
      (finSigmaFinEquiv.symm (Fin.cast hsum.symm ⟨s.val, hs⟩) : (i : Fin d) × Fin (w i)).1
      else ⟨0, hd⟩
    refine ⟨csel, fun s p q => decide (s.val < R - u) && p && q, fun h => ord h,
      fun s => ini (csel s), fun s => stp (csel s),
      fun s st => decide (s.val < R - u) && T (oP (csel s) st) && T (oQ (csel s) st), ?_⟩
    intro x
    simp only [hP, hQ, T, dcount]
    refine ⟨fun _ => trivial, ?_, ?_⟩
    · intro hall
      simp only [hall, Bool.and_true]
      have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin R)))
        (fun s : Fin R => (s : ℕ) < R - u)
      have h2 : (Finset.univ.filter (fun s : Fin R => (s : ℕ) < R - u)).card = R - u := by
        rw [Fin.card_filter_val_lt]; omega
      have h3 : (Finset.univ.filter (fun s : Fin R => decide ((s : ℕ) < R - u) = false))
          = Finset.univ.filter (fun s : Fin R => ¬ (s : ℕ) < R - u) := by
        apply Finset.filter_congr; intro s _; simp
      rw [h3]; rw [Finset.card_univ, Fintype.card_fin] at h1; omega
    · rintro ⟨j, hj⟩
      rw [Finset.card_eq_sum_card_fiberwise (f := csel) (t := Finset.univ) (by simp)]
      refine le_trans (Finset.sum_le_sum (fun h _ => ?_)) (hw j)
      split_ifs with hc
      · apply le_of_eq; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro s hs hcs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
          decide_eq_true_eq] at hs
        rw [hcs] at hs
        rcases hc with hc | hc
        · rw [← hc] at hs; rw [decide_eq_false_iff_not] at hj; exact hj hs.1.2
        · rw [← hc] at hs; rw [decide_eq_false_iff_not] at hj; exact hj hs.2
      · refine le_trans (Finset.card_le_card ?_) (fiber_le (R := R) w hsum h)
        intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
          decide_eq_true_eq] at hs ⊢
        refine ⟨hs.1.1.1, ?_⟩
        have h4 := hs.2
        simp only [csel, dif_pos hs.1.1.1] at h4
        exact h4
  · intro hn hM ⟨choose, decode, order, init, step, out, H⟩
    exact dir2 n r d R u v M menu hn hM choose decode
      (fun x seed => out seed ((List.finRange (2*n)).foldl
          (fun st k => step seed k st (x (order (choose seed) k))) (init seed))) H
