import sys
import textwrap

all_prev = []
for cur in sys.stdin:
    cur = cur.strip()

    cur, _, cur_f = cur.partition(' ')
    if not cur_f:
        cur_f = cur

    cur_f_base, _, _ = cur_f.partition(' ')
    if cur_f_base.startswith('@'):
        cur_f_base = cur_f_base[1:]

    if len(all_prev) != 0:
        prev, prev_f = all_prev[-1]
        print(textwrap.dedent(r'''

            Lemma {cur}_correct : hget (genv_denote {cur}_genv) {cur}_mb hnil = {cur_f}.
            unfold {cur_f_base}.
            autorewrite with oeuf_validation__{prev}.
            oeuf_refl.
            Qed.
            Hint Rewrite <- {cur}_correct : oeuf_validation__{cur}.

            Lemma {cur}_promote_eq : forall sg (mb : member sg {prev}_sigs),
                hget (genv_denote {prev}_genv) mb =
                hget (genv_denote {cur}_genv) ({cur}_promote sg mb).
            intros. oeuf_refl.
            Qed.

            Opaque {cur}_sigs {cur}_promote {cur}_genv {cur}_mb.
            Check {cur}_correct.

        ''').format(**locals()))
    else:
        print(textwrap.dedent(r'''

            Lemma {cur}_correct : hget (genv_denote {cur}_genv) {cur}_mb hnil = {cur_f}.
            unfold {cur_f_base}.
            oeuf_refl.
            Qed.
            Hint Rewrite <- {cur}_correct : oeuf_validation__{cur}.

            Opaque {cur}_sigs {cur}_promote {cur}_genv {cur}_mb.
            Check {cur}_correct.

        ''').format(**locals()))

    for (other, other_f) in all_prev:
        print(textwrap.dedent(r'''
            Lemma {other}_correct__at__{cur} : hget (genv_denote {cur}_genv) {other}_mb__at__{cur} hnil = {other_f}.
            unfold {other}_mb__at__{cur}.
            rewrite <- {cur}_promote_eq.
            apply {other}_correct.
            Qed.
            Hint Rewrite <- {other}_correct__at__{cur} : oeuf_validation__{cur}.
            Opaque {other}_mb__at__{cur}.
        ''').format(**locals()))

    all_prev.append((cur, cur_f))
    prev = cur

