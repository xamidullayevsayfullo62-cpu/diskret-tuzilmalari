# Diskret tuzilmalar yordamchisi — bitta fayl, bitta universal doska
# (mavzu masala matniga qarab avtomatik aniqlanadi)
#
# O'rnatish:  pip install flask werkzeug gunicorn
# Ishga tushirish:  python diskret_tuzilmalar.py   ->  http://localhost:5000
# Login/parol: APP_USER va APP_PASS muhit o'zgaruvchilari (standart: admin / admin12345)
# Maxfiy kalit: SECRET_KEY muhit o'zgaruvchisi (internetga chiqarishdan oldin o'zgartiring)

import os
import re
import math
from functools import wraps
from itertools import product, permutations, combinations
from collections import Counter

from flask import Flask, request, session, redirect, url_for, render_template_string, abort
from werkzeug.security import generate_password_hash, check_password_hash

MAX_LEN = 4000
MAX_N = 200


# ======================= UMUMIY YORDAMCHILAR =======================

def key(v):
    """Aralash turdagi elementlarni tartiblash uchun kalit (sonlar oldin, so'zlar keyin)."""
    if isinstance(v, (int, float)):
        return (0, v, "")
    return (1, 0, str(v))

def fset(s):
    if not s:
        return "∅"
    return "{" + ", ".join(str(x) for x in sorted(s, key=key)) + "}"

def fpair(t):
    return "(" + ",".join(str(x) for x in t) + ")"

def sp(pairs):
    """Juftliklarni tartiblangan ro'yxat sifatida qaytaradi."""
    return sorted(pairs, key=lambda p: tuple(key(x) for x in p))

def conv(x):
    x = x.strip().strip("'\"’")
    if re.fullmatch(r"-?\d+", x):
        return int(x)
    if re.fullmatch(r"-?\d+\.\d+", x):
        return float(x)
    return x

def expand_dots(body):
    """'1, 2, ..., 10' yoki '1, 3, 5, ..., 11' ni to'liq ro'yxatga aylantiradi."""
    parts = [x.strip() for x in body.split(",") if x.strip()]
    parts = [p.replace("\u2026", "...") for p in parts]
    if "..." not in parts:
        return [conv(x) for x in parts]
    i = parts.index("...")
    head = [conv(x) for x in parts[:i]]
    tail = [conv(x) for x in parts[i + 1:]]
    if len(head) >= 2 and tail and all(isinstance(v, int) for v in head + tail):
        step = head[-1] - head[-2]
        if step != 0:
            return head + list(range(head[-1] + step, tail[0] + 1, step))
    return head + tail

def named_sets(text):
    """'A = {1,2,3}' ko'rinishidagi to'plamlarni tartib bilan o'qiydi."""
    out = {}
    for name, body in re.findall(r"\b([A-Z])\s*=\s*\{([^{}]*)\}", text):
        if name not in out:
            out[name] = set(expand_dots(body))
    return out

def tuples(text):
    """(a,b) yoki (a,b,c) ko'rinishidagi tartiblangan n-liklarni o'qiydi."""
    out = []
    for body in re.findall(r"\(([^()]*)\)", text):
        out.append(tuple(conv(p) for p in body.split(",")))
    return out

def relation_named(text, name):
    m = re.search(r"\b%s\s*=\s*\{(.*?)\}" % name, text, re.S)
    if not m:
        return None
    return {t for t in tuples(m.group(1)) if len(t) == 2}

def relation(text):
    m = re.search(r"\bR\s*=\s*\{(.*?)\}", text, re.S)
    src = m.group(1) if m else text
    return {t for t in tuples(src) if len(t) == 2}

def rel_props(A, R):
    refl = [a for a in sorted(A, key=key) if (a, a) not in R]
    sb = [(a, b) for (a, b) in sp(R) if (b, a) not in R]
    ab = [(a, b) for (a, b) in sp(R) if a != b and (b, a) in R]
    tb = [(a, b, c) for (a, b) in sp(R) for (x, c) in sp(R) if b == x and (a, c) not in R]
    return refl, sb, ab, tb


# ======================= 1. DISKRET VA UZLUKSIZ =======================

FAMOUS = {
    "N": ("natural sonlar", "sanoqli (cheksiz)",
          "1, 2, 3, ... ketma-ketligi bilan elementlarini sanab chiqish mumkin."),
    "Z": ("butun sonlar", "sanoqli (cheksiz)",
          "0, 1, −1, 2, −2, ... tartibida sanab chiqish mumkin."),
    "Q": ("ratsional sonlar", "sanoqli (cheksiz)",
          "Kantorning zigzag usuli bilan sanab chiqish mumkin."),
    "R": ("haqiqiy sonlar", "sanoqsiz (uzluksiz)",
          "Kantorning diagonal usuli bilan isbotlanadi: R ni sanab bo'lmaydi."),
}

def solve_type(text):
    L = ["## Tahlil"]
    found = 0
    for name in dict.fromkeys(re.findall(r"\b([NZQR])\b", text)):
        nm, typ, why = FAMOUS[name]
        L.append(f"{name} — {nm}: {typ}. {why}")
        found += 1
    for lb, a, b, rb in re.findall(r"([\[\(])\s*(-?\d+(?:\.\d+)?)\s*,\s*(-?\d+(?:\.\d+)?)\s*([\]\)])", text):
        L.append(f"{lb}{a}, {b}{rb} oraliq: sanoqsiz (uzluksiz). Oraliqda cheksiz ko'p haqiqiy son bor, ularni sanab bo'lmaydi.")
        found += 1
    for body in re.findall(r"\{([^{}]*)\}", text):
        els = [x for x in body.split(",") if x.strip()]
        L.append(f"{{{body.strip()}}} — chekli to'plam, {len(els)} ta element. Diskret.")
        found += 1
    if not found:
        return ["✘ To'plam topilmadi. Masalan: N, Z, Q, R, [0,1], (2,5), {1,2,3}"]
    L.append("## Xulosa")
    L.append("Diskret to'plam: chekli yoki sanoqli (elementlarini ketma-ket sanab chiqish mumkin).")
    L.append("Uzluksiz to'plam: sanoqsiz (bunday sanash mumkin emas), masalan R yoki noldan farqli interval.")
    L.append("Eslatma: sanoqli to'plamlarning birlashmasi va dekart ko'paytmasi sanoqli, lekin R×R va 2^N sanoqsiz.")
    return L


# ======================= 2. TO'PLAMLAR USTIDA AMALLAR =======================

def solve_sets(text):
    S = named_sets(text)
    U = S.pop("U", None)
    if len(S) < 2:
        return ["✘ Kamida ikki to'plam kiriting. Masalan: A = {1,2,3}, B = {2,3,4}"]
    names = list(S.keys())
    a, b = names[0], names[1]
    A, B = S[a], S[b]

    L = ["## Berilgan to'plamlar"]
    for n_ in names:
        L.append(f"{n_} = {fset(S[n_])},   |{n_}| = {len(S[n_])}")
    if U is not None:
        L.append(f"U = {fset(U)}")
    else:
        L.append("Eslatma: U berilmagan, shuning uchun to'ldiruvchi (') hisoblanmadi.")

    L.append("## Asosiy amallar")
    L.append(f"{a} ∪ {b} = {fset(A | B)}      (A yoki B da bor elementlar)")
    L.append(f"{a} ∩ {b} = {fset(A & B)}      (ham A, ham B da bor elementlar)")
    L.append(f"{a} \\ {b} = {fset(A - B)}      (A da bor, B da yo'q)")
    L.append(f"{b} \\ {a} = {fset(B - A)}      (B da bor, A da yo'q)")
    L.append(f"{a} Δ {b} = {fset(A ^ B)}      (faqat bittasida bor)")
    if U is not None:
        L.append(f"{a}' = U \\ {a} = {fset(U - A)}")
        L.append(f"{b}' = U \\ {b} = {fset(U - B)}")
        lhs, rhs = U - (A | B), (U - A) & (U - B)
        mark = "✔ teng" if lhs == rhs else "✘ teng emas"
        L.append(f"De Morgan: ({a}∪{b})' = {fset(lhs)},  {a}'∩{b}' = {fset(rhs)}  →  {mark}")

    L.append("## Munosabatlar")
    L.append(f"{a} ⊆ {b}: " + ("ha" if A <= B else "yo'q"))
    L.append(f"{b} ⊆ {a}: " + ("ha" if B <= A else "yo'q"))
    L.append(f"{a} = {b}: " + ("ha" if A == B else "yo'q"))
    L.append(f"{a} va {b} kesishmaydimi: " + ("ha" if not (A & B) else "yo'q"))

    L.append("## Elementlar soni (quvvat)")
    L.append(f"|{a} ∪ {b}| = |{a}| + |{b}| − |{a} ∩ {b}| = {len(A)} + {len(B)} − {len(A & B)} = {len(A | B)}")
    L.append(f"|{a} Δ {b}| = |{a} ∪ {b}| − |{a} ∩ {b}| = {len(A | B)} − {len(A & B)} = {len(A ^ B)}")
    L.append(f"|{a} × {b}| = {len(A)} · {len(B)} = {len(A) * len(B)}")
    L.append(f"|P({a})| = 2^{len(A)} = {2 ** len(A)}")

    if len(A) <= 4:
        ps = [fset(c) for r in range(len(A) + 1) for c in combinations(sorted(A, key=key), r)]
        L.append(f"P({a}) = {{" + ", ".join(ps) + "}")
    if len(A) * len(B) <= 16:
        cp = [fpair((x, y)) for x in sorted(A, key=key) for y in sorted(B, key=key)]
        L.append(f"{a} × {b} = {{" + ", ".join(cp) + "}")

    if len(names) >= 3:
        c_name = names[2]
        C = S[c_name]
        L.append(f"## {a}, {b}, {c_name} uchun (uch to'plam)")
        L.append(f"|{a}∪{b}∪{c_name}| = |{a}|+|{b}|+|{c_name}| − |{a}∩{b}| − |{a}∩{c_name}| − |{b}∩{c_name}| + |{a}∩{b}∩{c_name}|")
        L.append(f"= {len(A)}+{len(B)}+{len(C)} − {len(A & B)} − {len(A & C)} − {len(B & C)} + {len(A & B & C)} = {len(A | B | C)}")
        L.append("Sohalar (faqat shu kombinatsiyada bo'lgan elementlar soni):")
        sets3 = [(a, A), (b, B), (c_name, C)]
        universe = U if U is not None else (A | B | C)
        for flags in product([True, False], repeat=3):
            cnt = sum(1 for x in universe
                      if all((x in st) == f for (_, st), f in zip(sets3, flags)))
            label = "∩".join(n_ if f else n_ + "'" for (n_, _), f in zip(sets3, flags))
            L.append(f"  {label}: {cnt}")
    return L


# ======================= 3. TARTIBLANGAN TO'PLAMLAR =======================

def first_diff(t1, t2):
    for i, (x, y) in enumerate(zip(t1, t2)):
        if x != y:
            return i, x, y
    return None

def solve_poset(A, R):
    L = ["## Qisman tartib tahlili", f"A = {fset(A)}"]
    refl, sb, ab, tb = rel_props(A, R)
    ok = not refl and not ab and not tb
    if not ok:
        L.append("✘ Bu munosabat qisman tartib emas (refleksiv, antisimmetrik va tranzitiv bo'lishi kerak).")
        return L
    L.append("✔ Qisman tartib: refleksiv, antisimmetrik va tranzitiv.")
    minimal = [a for a in sorted(A, key=key) if not any(b != a and (b, a) in R for b in A)]
    maximal = [a for a in sorted(A, key=key) if not any(b != a and (a, b) in R for b in A)]
    least = [a for a in sorted(A, key=key) if all((a, b) in R for b in A)]
    greatest = [a for a in sorted(A, key=key) if all((b, a) in R for b in A)]
    L.append("## Natija")
    L.append("Minimal elementlar: " + fset(minimal))
    L.append("Maksimal elementlar: " + fset(maximal))
    L.append("Eng kichik (least): " + (str(least[0]) if least else "yo'q"))
    L.append("Eng katta (greatest): " + (str(greatest[0]) if greatest else "yo'q"))
    return L

def solve_order(text):
    R = relation_named(text, "R")
    if R is not None:
        S = named_sets(text)
        A = set(S["A"]) if "A" in S else {x for p in R for x in p}
        return solve_poset(A, R)

    T = tuples(text)
    if not T:
        return ["✘ Juftliklarni (a,b) yoki n-liklarni (a,b,c) ko'rinishida kiriting. Masalan: (1,2), (1,3), (2,1)"]
    L = ["## Berilgan", ", ".join(fpair(t) for t in T),
         "## Leksikografik tartib qoidasi",
         "(a1,…,an) < (b1,…,bn) agar birinchi farq bo'lgan i-o'rinda ai < bi bo'lsa."]
    if len(set(T)) < len(T):
        L.append("Eslatma: takrorlangan juftliklar bir marta hisobga olindi.")
    S = sorted(set(T), key=lambda t: tuple(key(x) for x in t))
    L.append("## Saralash qadamlari")
    for t1, t2 in zip(S, S[1:]):
        d = first_diff(t1, t2)
        if d:
            L.append(f"{fpair(t1)} < {fpair(t2)}:  {d[0] + 1}-o'rinda {d[1]} < {d[2]}")
        else:
            L.append(f"{fpair(t1)} < {fpair(t2)}:  qisqaroq ketma-ketlik oldin keladi")
    L.append("## Natija")
    L.append("Tartib: " + " < ".join(fpair(t) for t in S))
    L.append(f"Eng kichik: {fpair(S[0])};   eng katta: {fpair(S[-1])}")
    return L


# ======================= 4. MUNOSABATLAR =======================

def solve_rel(text):
    R = relation(text)
    if not R:
        return ["✘ R munosabatni kiriting. Masalan: R = {(1,1),(2,2),(1,2),(2,1)}, A = {1,2}"]
    S = named_sets(text)
    A = set(S["A"]) if "A" in S else {x for p in R for x in p}

    L = ["## Berilgan", f"A = {fset(A)}",
         "R = {" + ", ".join(fpair(p) for p in sp(R)) + "}"]

    refl, sb, ab, tb = rel_props(A, R)
    L.append("## Xossalarni tekshirish")
    if refl:
        L.append(f"✘ Refleksiv emas: ({refl[0]},{refl[0]}) ∉ R")
    else:
        L.append("✔ Refleksiv: har bir a∈A uchun (a,a)∈R")
    if sb:
        a, b = sb[0]
        L.append(f"✘ Simmetrik emas: ({a},{b}) ∈ R, lekin ({b},{a}) ∉ R")
    else:
        L.append("✔ Simmetrik: (a,b)∈R bo'lsa (b,a)∈R")
    if ab:
        a, b = ab[0]
        L.append(f"✘ Antisimmetrik emas: ({a},{b}) va ({b},{a}) ikkalasi ham R da")
    else:
        L.append("✔ Antisimmetrik: (a,b) va (b,a) ∈ R bo'lsa a = b")
    if tb:
        a, b, c = tb[0]
        L.append(f"✘ Tranzitiv emas: ({a},{b}), ({b},{c}) ∈ R, lekin ({a},{c}) ∉ R")
    else:
        L.append("✔ Tranzitiv: (a,b),(b,c)∈R ⇒ (a,c)∈R")

    eq = not refl and not sb and not tb
    po = not refl and not ab and not tb
    L.append("## Xulosa")
    L.append(("✔ " if eq else "✘ ") + "Ekvivalentlik munosabati" + ("" if eq else " emas"))
    L.append(("✔ " if po else "✘ ") + "Qisman tartib" + ("" if po else " emas"))

    if po:
        L.extend(["## Tartib elementlari (qisman tartib sifatida)"] + solve_poset(A, R)[4:])

    if eq:
        L.append("## Ekvivalentlik sinflari")
        seen, classes = set(), []
        for a in sorted(A, key=key):
            if a in seen:
                continue
            cl = {b for b in A if (a, b) in R}
            seen |= cl
            classes.append((a, cl))
        for a, cl in classes:
            L.append(f"[{a}] = {fset(cl)}")
        L.append(f"Sinflar soni: {len(classes)}. Ular A ning bo'laklarini (rozbiyenie) hosil qiladi.")

    if tb:
        C = set(R)
        added = []
        changed = True
        while changed:
            changed = False
            for a, b in list(C):
                for x, c in list(C):
                    if b == x and (a, c) not in C:
                        C.add((a, c))
                        added.append((a, c))
                        changed = True
        L.append("## Tranzitiv yopilma R⁺")
        L.append("Qo'shilishi kerak bo'lgan juftliklar: " + ", ".join(fpair(p) for p in sp(added)))

    L.append("## Qo'shimcha amallar")
    L.append("R⁻¹ = {" + ", ".join(fpair((b, a)) for (a, b) in sp(R)) + "}")
    S2 = relation_named(text, "S")
    if S2:
        comp = {(a, c) for (a, b) in R for (x, c) in S2 if b == x}
        L.append("R∘S = {(a,c) | ∃b: (a,b)∈R va (b,c)∈S} = {" + ", ".join(fpair(p) for p in sp(comp)) + "}")
    return L


# ======================= 5. KOMBINATORIKA ASOSIY QOIDALARI =======================

def solve_comb_nk(text):
    low = text.lower()

    w = re.search(r"so[’']z\s*[:=]\s*([A-Za-z]+)", text)
    if w:
        word = w.group(1)
        n = len(word)
        cnt = Counter(word.upper())
        den = 1
        for c in cnt.values():
            den *= math.factorial(c)
        parts = ", ".join(f"{ch}:{c}" for ch, c in sorted(cnt.items()))
        return [
            "## So'zning harflari bilan o'rin almashtirish",
            f"So'z: {word}, uzunligi n = {n}",
            f"Harflar soni: {parts}",
            "Formula: n! / (n1!·n2!·…·nk!)",
            "= " + f"{n}! / (" + "·".join(f"{c}!" for _, c in sorted(cnt.items()))
            + f") = {math.factorial(n)} / {den} = {math.factorial(n) // den}",
        ]

    mn = re.search(r"\bn\s*=\s*(\d+)", text)
    if not mn:
        return ["✘ n = ... ni kiriting (masalan: n = 5, k = 2)."]
    n = int(mn.group(1))
    mk = re.search(r"\bk\s*=\s*(\d+)", text)
    k = int(mk.group(1)) if mk else None
    if n > MAX_N or (k is not None and k > MAX_N):
        return [f"✘ n va k {MAX_N} dan oshmasin."]

    L = ["## Berilgan: n = " + str(n) + (f", k = {k}" if k is not None else "")]
    L.append(f"P({n}) = {n}! = {math.factorial(n)}      — o'rin almashtirish (n ta elementning barcha tartibi)")
    if k is not None:
        if k <= n:
            L.append(f"A({n},{k}) = n!/(n−k)! = {n}!/{n - k}! = {math.perm(n, k)}      — o'rinlashtirish (tartib muhim)")
            L.append(f"C({n},{k}) = n!/(k!(n−k)!) = {math.comb(n, k)}      — guruhlash (tartib muhim emas)")
        else:
            L.append(f"k > n bo'lgani uchun A({n},{k}) = C({n},{k}) = 0")
        L.append(f"n^k = {n}^{k} = {n ** k}      — takrorli o'rinlashtirish")
        L.append(f"C(n+k−1,k) = C({n + k - 1},{k}) = {math.comb(n + k - 1, k)}      — takrorli guruhlash")

        if "shar" in low and k >= 1:
            L.append("## Shar va qutilar (n ta bir xil shar, k ta farqli quti)")
            L.append(f"Bo'sh qutilar ruxsat: C(n+k−1,k−1) = C({n + k - 1},{k - 1}) = {math.comb(n + k - 1, k - 1)}")
            if n >= k:
                L.append(f"Har qutida kamida 1 ta: C(n−1,k−1) = C({n - 1},{k - 1}) = {math.comb(n - 1, k - 1)}")
            else:
                L.append("Har qutida kamida 1 ta: n < k bo'lgani uchun 0")

        if re.search(r"binom|koeffitsient|\(x\s*\+\s*y\)", low) and k <= n:
            L.append(f"(x+y)^{n} ning x^{k}·y^{n - k} oldidagi koeffitsienti = C({n},{k}) = {math.comb(n, k)}")

        if n <= 4 and 1 <= k <= n:
            arr = list(permutations(range(1, n + 1), k))
            cmb = list(combinations(range(1, n + 1), k))
            L.append("## Ro'yxat (kichik misol)")
            L.append("O'rinlashtirishlar: " + ", ".join(fpair(p) for p in arr))
            L.append("Guruhlar: " + ", ".join(fset(c) for c in cmb))
    return L


def comb_direct(text):
    """C(10,3), A(5,2), P(4), 5! kabi ifodalarni hisoblaydi."""
    L = ["## Berilgan ifodalar hisobi"]
    for f, a, b in re.findall(r"\b([CAP])\s*\(\s*(\d+)\s*(?:,\s*(\d+))?\s*\)", text):
        n = int(a)
        if n > MAX_N:
            return [f"✘ n {MAX_N} dan oshmasin."]
        if f == "P" and not b:
            L.append(f"P({n}) = {n}! = {math.factorial(n)}")
        elif f in "CA" and b:
            k = int(b)
            if k > n:
                L.append(f"{f}({n},{k}) = 0      (k > n)")
            elif f == "C":
                L.append(f"C({n},{k}) = {n}!/({k}!·{n - k}!) = {math.comb(n, k)}")
            else:
                L.append(f"A({n},{k}) = {n}!/{n - k}! = {math.perm(n, k)}")
    for a in re.findall(r"\b(\d+)\s*!", text):
        n = int(a)
        if n > MAX_N:
            return [f"✘ n {MAX_N} dan oshmasin."]
        L.append(f"{n}! = {math.factorial(n)}")
    return L if len(L) > 1 else None


def comb_nl(text):
    """Oddiy so'zli masalalar: 'n ta ... dan k tasini ...' ko'rinishi (matndagi sonlar bo'yicha)."""
    low = text.lower()
    nums = [int(x) for x in re.findall(r"\d+", text)]
    if not nums:
        return None
    n = nums[0]
    k = nums[1] if len(nums) > 1 else None
    if k is None and re.search(r"qo'l siq|juftlik|juft", low):
        k = 2
        low += " tanlash"
    if n > MAX_N or (k is not None and k > MAX_N):
        return [f"✘ n va k {MAX_N} dan oshmasin."]
    rep = bool(re.search(r"takror|qaytar", low))
    unord = bool(re.search(r"tanla|guruh|komissiya|qo'mita|jamoa|kishilik|qo'l siq", low))
    ordd = bool(re.search(r"tartib|navbat|ketma-ket|kod|parol|raqam|lavozim|o'rinlash|o'tqaz|o'tir", low))
    perm_only = bool(re.search(r"almashtir|joylash|saf", low))

    if k is not None and re.search(r"\bshar|\bquti", low):
        sub = solve_comb_nk(f"n = {n}, k = {k}, shar")
        pick = "Shar-quti masalasi: pastdagi «Shar va qutilar» bo'limiga qarang."
    else:
        sub = solve_comb_nk(f"n = {n}" + (f", k = {k}" if k is not None else ""))
        if k is None or (perm_only and not unord):
            pick = f"Eng mos formula: P({n}) = {n}! = {math.factorial(n)}"
        elif rep and unord:
            pick = f"Eng mos formula (takrorli guruhlash): C(n+k−1,k) = {math.comb(n + k - 1, k)}"
        elif rep:
            pick = f"Eng mos formula (takrorli o'rinlashtirish): n^k = {n ** k}"
        elif unord and not ordd:
            pick = f"Eng mos formula (guruhlash, tartib muhim emas): C({n},{k}) = {math.comb(n, k) if k <= n else 0}"
        elif ordd and not unord:
            pick = f"Eng mos formula (o'rinlashtirish, tartib muhim): A({n},{k}) = {math.perm(n, k) if k <= n else 0}"
        else:
            pick = "Tartib muhimmi? Muhim bo'lsa A(n,k), muhim bo'lmasa C(n,k) ni oling."
    head = [f"## Matndan olingan sonlar: n = {n}" + (f", k = {k}" if k is not None else ""),
            pick,
            "Eslatma: so'zli masalada sonlar matndagi tartib bilan olindi. Noto'g'ri bo'lsa, «n = ..., k = ...» ko'rinishida yozing."]
    return head + sub


def solve_comb(text):
    text = text.replace("’", "'").replace("‘", "'")
    low = text.lower()
    if re.search(r"so'z\s*[:=]", low):
        return solve_comb_nk(re.sub(r"(?i)so'z", "so'z", text))
    w = re.search(r"\b([A-Z]{4,})\b", text) or re.search(r"[\"«“]([A-Za-z]{3,})[\"»”]", text)
    if w and re.search(r"so'z|harf|anagramm", low):
        return solve_comb_nk("so'z: " + w.group(1))
    d = comb_direct(text)
    if d:
        return d
    if re.search(r"\bn\s*=\s*\d", text):
        return solve_comb_nk(text)
    r = comb_nl(text)
    if r:
        return r
    return ["✘ n = ... (va k = ...) ni kiriting yoki masalani so'z bilan yozing: «10 ta talabadan 3 tasini necha usulda tanlash mumkin?»"]


# ======================= 6. KOMBINATORIKA: TO'PLAMLAR QUVVATI =======================

def solve_card(text):
    single = {x: int(v) for x, v in re.findall(r"\|\s*([A-Z])\s*\|\s*=\s*(\d+)", text)}
    pair = {}
    for x, op, y, v in re.findall(r"\|\s*([A-Z])\s*([∩∪])\s*([A-Z])\s*\|\s*=\s*(\d+)", text):
        pair[(op, *sorted([x, y]))] = int(v)
    triple = {}
    for x, y, z, v in re.findall(r"\|\s*([A-Z])\s*∩\s*([A-Z])\s*∩\s*([A-Z])\s*\|\s*=\s*(\d+)", text):
        triple[tuple(sorted([x, y, z]))] = int(v)

    if not single and not pair and not triple:
        return ["✘ Ma'lumot kiriting. Masalan: |A| = 10, |B| = 7, |A∩B| = 3"]

    L = ["## Berilgan qiymatlar"]
    for x, v in single.items():
        L.append(f"|{x}| = {v}")
    for (op, x, y), v in pair.items():
        L.append(f"|{x}{op}{y}| = {v}")
    for (x, y, z), v in triple.items():
        L.append(f"|{x}∩{y}∩{z}| = {v}")

    A, B = single.get("A"), single.get("B")
    AB = pair.get(("∩", "A", "B"))
    AUB = pair.get(("∪", "A", "B"))
    if A is not None and B is not None:
        L.append("## Ikki to'plam uchun")
        if AB is None and AUB is not None:
            AB = A + B - AUB
            L.append(f"|A∩B| = |A|+|B|−|A∪B| = {A}+{B}−{AUB} = {AB}")
        if AUB is None and AB is not None:
            AUB = A + B - AB
            L.append(f"|A∪B| = |A|+|B|−|A∩B| = {A}+{B}−{AB} = {AUB}")
        if AB is not None and (AB < 0 or AB > min(A, B)):
            L.append(f"✘ Ziddiyat: |A∩B| = {AB} qiymati |A| va |B| bilan mos emas (0 dan min(|A|,|B|) gacha bo'lishi kerak).")
        elif AB is not None:
            L.append(f"|A\\B| = |A|−|A∩B| = {A}−{AB} = {A - AB}")
            L.append(f"|B\\A| = |B|−|A∩B| = {B}−{AB} = {B - AB}")
            L.append(f"|A△B| = |A|+|B|−2|A∩B| = {A}+{B}−2·{AB} = {A + B - 2 * AB}")
        L.append(f"|A×B| = |A|·|B| = {A}·{B} = {A * B}")

    if A is not None:
        L.append(f"|P(A)| = 2^|A| = 2^{A} = {2 ** A}")

    C = single.get("C")
    BC = pair.get(("∩", "B", "C"))
    AC = pair.get(("∩", "A", "C"))
    ABC = triple.get(("A", "B", "C"))
    if None not in (A, B, C, AB, BC, AC, ABC):
        L.append("## Uch to'plam uchun")
        total = A + B + C - AB - AC - BC + ABC
        L.append("|A∪B∪C| = |A|+|B|+|C| − |A∩B| − |A∩C| − |B∩C| + |A∩B∩C|")
        L.append(f"= {A}+{B}+{C} − {AB} − {AC} − {BC} + {ABC} = {total}")

    X, Y = single.get("X"), single.get("Y")
    if X is not None and Y is not None:
        L.append(f"## Funksiyalar: |X| = {X}, |Y| = {Y}")
        L.append(f"Barcha funksiyalar X→Y: |Y|^|X| = {Y}^{X} = {Y ** X}")
        L.append(f"In'ektiv (o'zaro bir qiymatli): A({Y},{X}) = {math.perm(Y, X)}")
        sur = sum((-1) ** i * math.comb(Y, i) * (Y - i) ** X for i in range(Y + 1))
        L.append(f"Syrektiv (inklyuziya-ekskluziya): Σ(−1)^i·C({Y},i)·({Y}−i)^{X} = {sur}")
        L.append("Biyektiv: " + (f"{X}! = {math.factorial(X)}" if X == Y else "0 (|X| ≠ |Y|)"))
    return L


# ======================= 7. MULOHAZALAR (MANTIQ) =======================

OPS = {"¬": "¬", "~": "¬", "!": "¬", "not": "¬",
       "∧": "∧", "&": "∧", "and": "∧", "va": "∧",
       "∨": "∨", "|": "∨", "or": "∨", "yoki": "∨",
       "→": "→", "->": "→",
       "↔": "↔", "<->": "↔"}

TOK = re.compile(r"\s*(<->|↔|->|→|¬|~|!|∧|&|∨|\||\(|\)|\bnot\b|\band\b|\bor\b|\bva\b|\byoki\b|[A-Za-z][A-Za-z0-9_]*|[01])")

def tokenize(s):
    toks, pos = [], 0
    while True:
        m = TOK.match(s, pos)
        if not m:
            rest = s[pos:].strip()
            if not rest:
                break
            raise ValueError(f"Noma'lum belgi: '{rest[0]}'")
        toks.append(OPS.get(m.group(1), m.group(1)))
        pos = m.end()
    return toks

class Parser:
    """Ustuvorlik: ¬ > ∧ > ∨ > → > ↔. Implikatsiya o'ngdan chapga bog'lanadi."""
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def eat(self, want=None):
        tok = self.peek()
        if tok is None:
            raise ValueError("Ifoda to'liq emas (qavs yoki o'zgaruvchi yetishmaydi)")
        if want is not None and tok != want:
            raise ValueError(f"'{want}' kutilgan edi, lekin '{tok}' topildi")
        self.i += 1
        return tok

    def parse(self):
        e = self.iff()
        if self.peek() is not None:
            raise ValueError(f"Ortiqcha belgi: '{self.peek()}'")
        return e

    def iff(self):
        e = self.imp()
        while self.peek() == "↔":
            self.eat()
            e = ("↔", e, self.imp())
        return e

    def imp(self):
        e = self.disj()
        if self.peek() == "→":
            self.eat()
            return ("→", e, self.imp())
        return e

    def disj(self):
        e = self.conj()
        while self.peek() == "∨":
            self.eat()
            e = ("∨", e, self.conj())
        return e

    def conj(self):
        e = self.neg()
        while self.peek() == "∧":
            self.eat()
            e = ("∧", e, self.neg())
        return e

    def neg(self):
        tok = self.peek()
        if tok == "¬":
            self.eat()
            return ("¬", self.neg())
        if tok == "(":
            self.eat()
            e = self.iff()
            self.eat(")")
            return e
        tok = self.eat()
        if tok in ("0", "1"):
            return ("const", tok == "1")
        if re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", tok):
            return ("var", tok)
        raise ValueError(f"Kutilmagan belgi: '{tok}'")

def parse(s):
    toks = tokenize(s)
    if not toks:
        raise ValueError("Ifoda bo'sh")
    return Parser(toks).parse()

def ev(n, env):
    op = n[0]
    if op == "var":
        return env[n[1]]
    if op == "const":
        return n[1]
    if op == "¬":
        return not ev(n[1], env)
    a, b = ev(n[1], env), ev(n[2], env)
    if op == "∧":
        return a and b
    if op == "∨":
        return a or b
    if op == "→":
        return (not a) or b
    return a == b  # ↔

def vars_of(n):
    if n[0] == "var":
        return {n[1]}
    if n[0] == "const":
        return set()
    out = set()
    for c in n[1:]:
        out |= vars_of(c)
    return out

def rows(vs):
    for vals in product([True, False], repeat=len(vs)):
        yield dict(zip(vs, vals))

def bit(b):
    return "1" if b else "0"

def solve_formula(s):
    f = parse(s)
    vs = sorted(vars_of(f))
    if len(vs) > 6:
        return ["✘ 6 tadan ko'p o'zgaruvchi bo'lmasin."]
    envs = list(rows(vs))
    res = [ev(f, e) for e in envs]
    L = [f"## Ifoda: {s}", "O'zgaruvchilar: " + (", ".join(vs) if vs else "yo'q"),
         "## Rostlik jadvali", " ".join(vs) + " │ natija"]
    for env, r in zip(envs, res):
        L.append(" ".join(bit(env[v]) for v in vs) + " │ " + bit(r))
    L.append("## Xulosa")
    if all(res):
        L.append("✔ Tavtologiya: ifoda har doim rost.")
    elif not any(res):
        L.append("✘ Ziddiyat: ifoda har doim yolg'on.")
    else:
        L.append("Bajariladigan: ifoda ba'zan rost, ba'zan yolg'on.")
    if vs:
        if any(res):
            terms = ["(" + " ∧ ".join(v if e[v] else "¬" + v for v in vs) + ")"
                     for e, r in zip(envs, res) if r]
            L.append("Mukammal DNF: " + " ∨ ".join(terms))
        if not all(res):
            clauses = ["(" + " ∨ ".join("¬" + v if e[v] else v for v in vs) + ")"
                       for e, r in zip(envs, res) if not r]
            L.append("Mukammal KNF: " + " ∧ ".join(clauses))
    return L

def solve_equiv(s):
    sep = "≡" if "≡" in s else "=="
    a, b = s.split(sep, 1)
    f, g = parse(a), parse(b)
    vs = sorted(vars_of(f) | vars_of(g))
    L = [f"F = {a.strip()}", f"G = {b.strip()}", "## Rostlik jadvali",
         " ".join(vs) + " │ F G"]
    diff = None
    for env in rows(vs):
        x, y = ev(f, env), ev(g, env)
        L.append(" ".join(bit(env[v]) for v in vs) + " │ " + bit(x) + " " + bit(y))
        if x != y and diff is None:
            diff = env
    L.append("## Xulosa")
    if diff is None:
        L.append("✔ F ≡ G: ifodalar ekvivalent (barcha satrlarda qiymatlari teng).")
    else:
        L.append("✘ F ≡ G emas. Qarshi misol: " + ", ".join(f"{v}={bit(diff[v])}" for v in vs))
    return L

def solve_argument(s):
    sep = "⊢" if "⊢" in s else "|-"
    left, concl = s.split(sep, 1)
    prem_src = [p.strip() for p in left.split(",") if p.strip()]
    prem = [parse(p) for p in prem_src]
    C = parse(concl)
    vs = sorted(set().union(*(vars_of(f) for f in prem + [C])))

    L = ["## Argument"]
    for i, p in enumerate(prem_src, 1):
        L.append(f"P{i}: {p}")
    L.append(f"Xulosa: {concl.strip()}")
    L.append("## Rostlik jadvali")
    L.append(" ".join(vs) + " │ " + " ".join(f"P{i}" for i in range(1, len(prem) + 1)) + " │ Xulosa")
    counter = None
    for env in rows(vs):
        pv = [ev(p, env) for p in prem]
        cv = ev(C, env)
        L.append(" ".join(bit(env[v]) for v in vs) + " │ " + " ".join(bit(x) for x in pv) + " │ " + bit(cv))
        if all(pv) and not cv and counter is None:
            counter = env
    L.append("## Xulosa")
    if counter is None:
        L.append("✔ Argument TO'G'RI: barcha premislar rost bo'lganda xulosa ham rost.")
    else:
        L.append("✘ Argument NOTO'G'RI. Qarshi misol: " + ", ".join(f"{v}={bit(counter[v])}" for v in vs))
    return L

def solve_logic(text):
    s = text.split(":", 1)[1] if ":" in text else text
    s = s.strip()
    if "⊢" in s or "|-" in s:
        return solve_argument(s)
    if "≡" in s or "==" in s:
        return solve_equiv(s)
    return solve_formula(s)


# ======================= MA'LUMOTLAR (NAZARIYA, MISOLLAR) =======================

TOPICS = {
    1: "Diskret va uzluksiz to'plamlar",
    2: "To'plamlar ustida amallar",
    3: "Tartiblangan to'plamlar",
    4: "Munosabatlar turlari",
    5: "Kombinatorikaning asosiy qoidalari",
    6: "Kombinatorika: to'plamlar quvvati",
    7: "Mulohazalar ustida mantiqiy amallar",
}

THEORY = {
    1: "Diskret to'plam chekli yoki sanoqli bo'ladi: elementlarini 1, 2, 3, ... tartibida sanab chiqish mumkin. "
       "Uzluksiz (sanoqsiz) to'plam, masalan [0,1] oraliq yoki R, bunday sanashga ko'na olmaydi.",
    2: "Birlashma (∪), kesishma (∩), ayirma (\\), simmetrik ayirma (Δ) va to'ldiruvchi (') amallari. "
       "De Morgan qonunlari: (A∪B)' = A'∩B' va (A∩B)' = A'∪B'. Uch to'plam uchun qo'shish-ayirish formulasi ishlatiladi.",
    3: "Tartiblangan juftlik (a,b) va n-lik. Leksikografik tartib: birinchi farq bo'lgan o'rinda kichik element avval keladi. "
       "Qisman tartib: refleksiv, antisimmetrik va tranzitiv munosabat. Minimal, maksimal, eng kichik va eng katta elementlar aniqlanadi.",
    4: "R ⊆ A×A munosabat. Refleksiv: (a,a)∈R. Simmetrik: (a,b)∈R ⇒ (b,a)∈R. Antisimmetrik: (a,b),(b,a)∈R ⇒ a=b. "
       "Tranzitiv: (a,b),(b,c)∈R ⇒ (a,c)∈R. Ekvivalentlik = refleksiv + simmetrik + tranzitiv; qisman tartib = refleksiv + antisimmetrik + tranzitiv.",
    5: "Qo'shish va ko'paytirish qoidalari. O'rin almashtirish P(n)=n!, o'rinlashtirish A(n,k)=n!/(n−k)!, "
       "guruhlash C(n,k)=n!/(k!(n−k)!). Takrorli o'rinlashtirish n^k, takrorli guruhlash C(n+k−1,k). So'zlar uchun n!/(n1!·n2!·…).",
    6: "Chekli to'plam quvvati |A|. |A∪B| = |A|+|B|−|A∩B|, |A×B| = |A|·|B|, |P(A)| = 2^|A|. "
       "Funksiyalar soni |Y|^|X|. In'ektiv funksiyalar A(m,n), syrektiv funksiyalar inklyuziya-ekskluziya formulasi bilan topiladi.",
    7: "Mulohaza — rost yoki yolg'on qiymat qabul qiluvchi ifoda. Amallar: ¬ (inkor), ∧ (va), ∨ (yoki), → (implikatsiya), ↔ (ekvivalentlik). "
       "Tavtologiya — har doim rost, ziddiyat — har doim yolg'on. Argument to'g'ri bo'ladi, agar barcha premislar rost bo'lganda xulosa ham rost bo'lsa.",
}

EXAMPLES = {
    1: ["N, Z, Q va R to'plamlarini tahlil qiling", "[0,1] va (2,5) oraliqlari", "A = {1,2,3,4,5}"],
    2: ["A = {1,2,3}, B = {2,3,4}, U = {1,2,3,4,5}",
        "A = {1,2}, B = {1,2,3,4}, C = {2,4,6}"],
    3: ["(1,2), (1,3), (2,1), (2,3)",
        "(3,1,2), (1,5,4), (1,5,2)",
        "A = {1,2,3,4}, R = {(1,1),(2,2),(3,3),(4,4),(1,2),(1,3),(1,4),(2,4),(3,4)}"],
    4: ["R = {(1,1),(2,2),(3,3),(1,2),(2,1)}, A = {1,2,3}",
        "R = {(1,2),(2,3)}, A = {1,2,3}",
        "R = {(1,1),(2,2),(3,3),(1,2),(2,3),(1,3)}, S = {(1,1),(2,3)}, A = {1,2,3}"],
    5: ["n = 5, k = 2", "so'z: MISSISSIPPI", "n = 5, k = 3, shar, bo'sh qutilar ruxsat",
        "C(10,3)", "10 ta talabadan 3 kishilik guruhni necha usulda tanlash mumkin?"],
    6: ["|A| = 10, |B| = 7, |A∩B| = 3",
        "|A| = 5, |B| = 4, |C| = 3, |A∩B| = 2, |A∩C| = 1, |B∩C| = 1, |A∩B∩C| = 0",
        "|X| = 3, |Y| = 2"],
    7: ["(p ∧ q) → r", "p → q, p ⊢ q", "(p → q) ≡ (¬p ∨ q)", "¬(p ∨ q) ↔ (¬p ∧ ¬q)"],
}


# ======================= UNIVERSAL DOSKA: MAVZUNI AVTOMATIK ANIQLASH =======================

SOLVERS = {1: solve_type, 2: solve_sets, 3: solve_order, 4: solve_rel,
           5: solve_comb, 6: solve_card, 7: solve_logic}

RE_CARD = re.compile(r"\|\s*[A-Z]\s*(?:[∩∪]\s*[A-Z]\s*)*\|\s*=\s*\d+")
RE_REL = re.compile(r"\bR\s*=\s*\{\s*\(")
RE_LOGIC_SYM = re.compile(r"[⊢≡∧∨¬→↔]|<->|->|\|-|==")
RE_LOGIC_WORD = re.compile(
    r"(?<![A-Za-z])[a-z]\s+(?:and|or|va|yoki)\s+\(?\s*[¬~!]?\s*[a-z](?![A-Za-z])|\bnot\s+[a-z](?![A-Za-z])")
RE_COMB_STRONG = re.compile(
    r"so['’‘]z\s*[:=]|\b[CAP]\s*\(\s*\d+|\b\d+\s*!|\bn\s*=\s*\d", re.I)
RE_COMB_WORDS = re.compile(
    r"\bnecha\b|usulda|tanlash|tanlanadi|tanlab|o'rin\s*almashtir|navbat|komissiya|qo'mita|guruh|jamoa|"
    r"almashtir|joylash|anagramm|harflar|binom|koeffitsient|kombinatorika|ko'paytirish qoidasi|"
    r"qo'shish qoidasi|\bshar|\bquti|qo'l siq")
RE_TYPE_WORDS = re.compile(r"diskret|uzluksiz|sanoqli|sanoqsiz|oraliq|interval|kesma|cheksiz")
RE_BRACKET_INT = re.compile(r"\[\s*-?\d+(?:\.\d+)?\s*,\s*-?\d+(?:\.\d+)?\s*[\]\)]")
RE_FAMOUS = re.compile(r"(?<![A-Za-z])[NZQR](?![A-Za-z]|\s*=)")
RE_SET_WORDS = re.compile(r"birlashma|kesishma|ayirma|de\s*morgan|to'ldiruvchi|quvvat|dekart|bulean")
RE_ORDER_WORDS = re.compile(r"qisman tartib|minimal|maksimal|hasse|eng kichik|eng katta|poset")


def detect(text):
    """Masala matniga qarab mavzu raqamini (1–7) qaytaradi; topilmasa None."""
    t = text.replace("’", "'").replace("‘", "'")
    low = t.lower()

    if RE_CARD.search(t):
        return 6
    if RE_REL.search(t):
        if "leksikograf" in low:
            return 3
        if RE_ORDER_WORDS.search(low) and "ekvivalent" not in low:
            return 3
        return 4
    if RE_LOGIC_SYM.search(t) or RE_LOGIC_WORD.search(t):
        return 7
    if RE_COMB_STRONG.search(t):
        return 5
    if re.search(r"\b[A-Z]{4,}\b", t) and re.search(r"so'z|harf|anagramm", low):
        return 5
    is_interval = RE_TYPE_WORDS.search(low) or RE_BRACKET_INT.search(t)
    if (len(tuples(t)) >= 1 and re.search(r"\(\s*[^()]*,[^()]*\)", t)
            and not RE_COMB_WORDS.search(low) and not is_interval):
        return 3
    if re.search(r"\d", t) and RE_COMB_WORDS.search(low):
        return 5
    if RE_TYPE_WORDS.search(low) or RE_BRACKET_INT.search(t) or RE_FAMOUS.search(t):
        return 1
    S = named_sets(t)
    S.pop("U", None)
    if len(S) >= 2 or (S and RE_SET_WORDS.search(low)):
        return 2
    if re.search(r"\{[^{}]*\}", t):
        return 1
    return None


def split_problems(text):
    """Bir nechta masalani bo'sh qator yoki '1)', '2.' raqamlari bo'yicha ajratadi."""
    parts = re.split(r"\n\s*\n|\n(?=\s*\d+[\).]\s)", text.strip())
    out = []
    for p in parts:
        p = re.sub(r"^\s*\d+[\).]\s+", "", p).strip()
        if p:
            out.append(p)
    return out[:10]


HELP_LINES = [
    "✘ Mavzuni aniqlay olmadim. Masalani quyidagi ko'rinishlardan birida yozing:",
    "• To'plamlar: A = {1,2,3}, B = {2,3,4}, U = {1,2,3,4,5}",
    "• Munosabat: R = {(1,1),(2,2),(1,2)}, A = {1,2}",
    "• Kombinatorika: n = 5, k = 2   yoki   C(10,3)   yoki   so'z: MISSISSIPPI",
    "• Quvvat: |A| = 10, |B| = 7, |A∩B| = 3",
    "• Mantiq: (p ∧ q) → r   yoki   p → q, p ⊢ q",
    "• Tartib: (1,2), (1,3), (2,1)",
]


def solve_any(text):
    """Bitta yoki bir nechta masalani yechadi. Har bir masala uchun lug'at qaytaradi."""
    blocks = []
    for i, b in enumerate(split_problems(text), 1):
        tid = detect(b)
        if tid is None:
            lines = list(HELP_LINES)
        else:
            try:
                lines = SOLVERS[tid](b)
            except ValueError as e:
                lines = [f"✘ {e}"]
            except Exception:
                lines = ["✘ Ma'lumotni tushunib bo'lmadi. Formatni tekshiring yoki tayyor misollardan foydalaning."]
        blocks.append({
            "i": i,
            "q": b,
            "topic": TOPICS.get(tid),
            "theory": THEORY.get(tid),
            "lines": [classify(x) for x in lines],
        })
    return blocks


# ======================= VEB-ILOVA (BITTA UNIVERSAL DOSKA) =======================

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", "ozgartiring-bu-kalitni")

USERS = {
    os.environ.get("APP_USER", "admin"): generate_password_hash(os.environ.get("APP_PASS", "admin12345")),
}

CSS = """
:root{--bg:#f5f7fb;--card:#fff;--txt:#1b2333;--mut:#64748b;--acc:#4f46e5;--acc2:#7c3aed;--line:#e2e8f0;--ok:#059669;--bad:#dc2626;--code:#f1f5f9}
@media (prefers-color-scheme:dark){:root{--bg:#0b1120;--card:#141c2e;--txt:#e2e8f0;--mut:#94a3b8;--acc:#818cf8;--acc2:#a78bfa;--line:#263247;--ok:#34d399;--bad:#f87171;--code:#0f172a}}
*{box-sizing:border-box}
body{margin:0;font-family:system-ui,-apple-system,"Segoe UI",sans-serif;background:var(--bg);color:var(--txt)}
header{background:linear-gradient(135deg,var(--acc),var(--acc2));color:#fff;padding:14px 24px;display:flex;justify-content:space-between;align-items:center}
.brand{font-size:20px;font-weight:700}
.brand span{font-weight:400;font-size:15px;opacity:.85;margin-left:6px}
header a{color:#fff;opacity:.85;font-size:13px;text-decoration:none}
main{padding:24px;max-width:980px;margin:0 auto;width:100%}
.card{background:var(--card);border:1px solid var(--line);border-radius:18px;padding:20px 22px;margin-bottom:18px;box-shadow:0 6px 24px rgba(15,23,42,.05)}
.card h3{margin:0 0 10px;font-size:16px}
.lead{margin:0 0 12px;color:var(--mut);font-size:14.5px;line-height:1.55}
label{font-weight:600;font-size:14px;display:block;margin-bottom:8px}
textarea{width:100%;min-height:150px;border:1px solid var(--line);border-radius:12px;padding:14px;font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:15px;background:var(--code);color:var(--txt);resize:vertical}
textarea:focus,input:focus{outline:2px solid var(--acc);border-color:transparent}
.syms{display:flex;flex-wrap:wrap;gap:6px;margin:10px 0 0}
.sym{background:var(--code);border:1px solid var(--line);color:var(--txt);border-radius:8px;min-width:34px;padding:5px 8px;font-size:15px;cursor:pointer;font-family:inherit}
.sym:hover{border-color:var(--acc)}
details.ex{margin:14px 0}
details.ex summary{cursor:pointer;font-weight:600;font-size:14px;color:var(--acc)}
.exrow{margin-top:10px}
.exrow small{display:block;color:var(--mut);font-size:12px;margin-bottom:4px}
.chips{display:flex;flex-wrap:wrap;gap:8px}
.chip{background:transparent;border:1px solid var(--line);color:var(--acc);border-radius:999px;padding:6px 12px;font-size:12.5px;cursor:pointer;font-family:inherit;text-align:left}
.chip:hover{border-color:var(--acc)}
.go,.copy{background:linear-gradient(135deg,var(--acc),var(--acc2));color:#fff;border:0;border-radius:12px;padding:11px 22px;font-size:15px;font-weight:600;cursor:pointer;font-family:inherit}
.copy{padding:7px 14px;font-size:13px}
.hint{color:var(--mut);font-size:12.5px;margin-left:10px}
.res-head{display:flex;justify-content:space-between;align-items:center;gap:10px;margin-bottom:10px;flex-wrap:wrap}
.res-head h3{margin:0}
.badge{display:inline-block;background:var(--code);border:1px solid var(--line);color:var(--acc);border-radius:999px;padding:3px 12px;font-size:13px;font-weight:600;margin-left:6px}
.qecho{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:13px;color:var(--mut);background:var(--code);border-radius:10px;padding:8px 12px;margin:0 0 10px;white-space:pre-wrap;word-break:break-word}
details.th{margin:0 0 6px;font-size:14px;color:var(--mut)}
details.th summary{cursor:pointer;color:var(--acc);font-weight:600}
details.th p{margin:8px 0 0;line-height:1.6}
.ln{white-space:pre-wrap;font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:14px;line-height:1.7}
.ln.h{font-family:system-ui,sans-serif;font-weight:700;font-size:15px;color:var(--acc);margin-top:14px}
.ln.ok{color:var(--ok)}
.ln.bad{color:var(--bad)}
.err{color:var(--bad);font-weight:600}
.hist{list-style:none;padding:0;margin:0;font-size:14px}
.hist li{padding:8px 0;border-bottom:1px solid var(--line)}
.hist a{color:var(--acc);text-decoration:none;cursor:pointer}
.login-wrap{min-height:100vh;display:grid;place-items:center;padding:20px}
.login-card{width:100%;max-width:380px}
.login-card h2{margin:0 0 4px}
.login-card p{color:var(--mut);margin:0 0 18px;font-size:14px}
input{width:100%;border:1px solid var(--line);border-radius:12px;padding:12px 14px;font-size:15px;font-family:inherit;background:var(--code);color:var(--txt);margin-bottom:14px}
.login-card .go{width:100%}
@media (max-width:820px){main{padding:14px}header{padding:12px 14px}}
"""

LOGIN = """<!doctype html><html lang="uz"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Kirish · Diskret tuzilmalar</title>
<style>{{ css|safe }}</style></head>
<body><div class="login-wrap"><form method="post" class="card login-card">
<h2>∑ Diskret tuzilmalar</h2><p>Davom etish uchun tizimga kiring.</p>
<label>Login</label><input name="username" required autofocus>
<label>Parol</label><input type="password" name="password" required>
{% if err %}<p class="err">{{ err }}</p>{% endif %}
<button class="go" type="submit">Kirish</button></form></div></body></html>
"""

PAGE = """<!doctype html><html lang="uz"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Universal doska · Diskret tuzilmalar</title>
<style>{{ css|safe }}</style></head>
<body>
<header><div class="brand">∑ Diskret tuzilmalar<span>universal doska</span></div>
</header>
<main>
<section class="card">
<p class="lead">Istalgan masalani shu yerga yozing: to'plamlar, munosabatlar, tartib, kombinatorika, quvvat yoki mantiq.
Dastur mavzuni o'zi aniqlaydi va qadamma-qadam yechadi. Bir nechta masalani bo'sh qator bilan ajratib kiritish mumkin.</p>
<form method="post" id="f">
<label for="q">Masala</label>
<textarea id="q" name="q" placeholder="Masalan: A = {1,2,3}, B = {2,3,4}, U = {1,2,3,4,5}" autofocus>{{ q }}</textarea>
<div class="syms">{% for s in syms %}<button type="button" class="sym" data-s="{{ s }}">{{ s }}</button>{% endfor %}</div>
<details class="ex"><summary>Tayyor misollar</summary>
{% for name, items in examples %}<div class="exrow"><small>{{ name }}</small>
<div class="chips">{% for ex in items %}<button type="button" class="chip" data-v="{{ ex }}">{{ ex }}</button>{% endfor %}</div></div>{% endfor %}
</details>
<button class="go" type="submit">Yechish</button><span class="hint">Ctrl + Enter</span>
</form>
{% if err %}<p class="err">{{ err }}</p>{% endif %}
</section>
{% for b in blocks %}
<section class="card">
<div class="res-head"><h3>{% if blocks|length > 1 %}Masala {{ b.i }}{% else %}Yechim{% endif %}
{% if b.topic %}<span class="badge">{{ b.topic }}</span>{% endif %}</h3>
<button class="copy" type="button" data-t="res{{ b.i }}">Nusxalash</button></div>
{% if blocks|length > 1 %}<div class="qecho">{{ b.q }}</div>{% endif %}
{% if b.theory %}<details class="th"><summary>Nazariya</summary><p>{{ b.theory }}</p></details>{% endif %}
<div id="res{{ b.i }}">{% for cls, line in b.lines %}<div class="ln {{ cls }}">{{ line }}</div>{% endfor %}</div>
</section>
{% endfor %}
{% if hist %}
<section class="card"><h3>Oxirgi so'rovlar</h3>
<ul class="hist">{% for h in hist %}<li><a data-v="{{ h }}">{{ h }}</a></li>{% endfor %}</ul>
</section>
{% endif %}
</main>
<script>
var q = document.getElementById('q');
document.querySelectorAll('.chip,.hist a').forEach(function(b){ b.onclick = function(){ q.value = b.dataset.v; q.focus(); }; });
document.querySelectorAll('.sym').forEach(function(b){ b.onclick = function(){
  q.setRangeText(b.dataset.s, q.selectionStart, q.selectionEnd, 'end'); q.focus(); }; });
document.querySelectorAll('.copy').forEach(function(b){ b.onclick = function(){
  navigator.clipboard.writeText(document.getElementById(b.dataset.t).innerText); }; });
q.addEventListener('keydown', function(e){ if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') document.getElementById('f').requestSubmit(); });
</script>
</body></html>
"""

SYMS = ["∧", "∨", "¬", "→", "↔", "⊢", "≡", "∪", "∩", "Δ", "∅", "×", "⊆", "∈"]
EXAMPLE_GROUPS = [
    ("To'plamlar", EXAMPLES[2] + EXAMPLES[1]),
    ("Munosabat va tartib", EXAMPLES[4] + EXAMPLES[3]),
    ("Kombinatorika va quvvat", EXAMPLES[5] + EXAMPLES[6]),
    ("Mantiq", EXAMPLES[7]),
    ("Bir nechta masala birdan", ["A = {1,2,3}, B = {2,3,4}\n\nn = 6, k = 2\n\n(p → q) ≡ (¬p ∨ q)"]),
]


def login_required(f):
    return f

def classify(line):
    if line.startswith("## "):
        return ("h", line[3:])
    if line.startswith("✔"):
        return ("ok", line)
    if line.startswith("✘"):
        return ("bad", line)
    return ("", line)

@app.route("/", methods=["GET", "POST"])
@login_required
def index():
    q, blocks, err = "", [], None
    if request.method == "POST":
        q = request.form.get("q", "").strip()[:MAX_LEN]
        if not q:
            err = "Iltimos, masalani kiriting."
        else:
            blocks = solve_any(q)
            # Tarix: cookie hajmi cheklangani uchun qisqa va oz saqlanadi
            short = " ".join(q.split())[:60]
            old = [h for h in session.get("hist", []) if h != short]
            session["hist"] = ([short] + old)[:6]
    return render_template_string(
        PAGE, css=CSS, q=q, blocks=blocks, err=err, syms=SYMS,
        examples=EXAMPLE_GROUPS, hist=session.get("hist", []), user="mehmon",
    )

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)), debug=False)
