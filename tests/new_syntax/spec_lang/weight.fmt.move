module 0x42::m {
    struct S has drop {
        v: vector<u64>
    }

    fun sum(s: &S): u64 {
        let i = 0;
        let r = 0;
        while (i < s.v.length()) {
            r = r + s.v[i];
            i = i + 1;
        };
        r
    }

    spec sum {
        ensures result == spec_sum(s.v, len(s.v));
        ensures forall k: num [weight = 3]: k >= 0 ==> spec_sum(s.v, k) >= 0;
        ensures forall k: num, j: num { spec_sum(s.v, k), spec_sum(s.v, j) } [weight = 2]: k
            <= j ==> spec_sum(s.v, k) <= spec_sum(s.v, j);
        ensures exists first_long_binding_name: num, second_long_binding_name_that_is_longer: num
            [weight = 4]:
            first_long_binding_name <= second_long_binding_name_that_is_longer;
    } proof {
        forall v: vector<u64> , n: num { spec_sum(v, n) } [weight = 2] apply sum_nonneg(v, n);
    }
}

spec 0x42::m {
    spec fun spec_sum(v: vector<u64>, n: num): num [weight = 15] {
        if (n == 0) { 0 }
        else {
            spec_sum(v, n - 1) + v[n - 1]
        }
    }

    spec fun tight(a: u64, b: u64): bool [weight = 50] {
        a <= b
    }

    spec fun a_function_with_a_rather_long_name(
        first_argument: vector<u64>, second_argument: num
    ): num [weight = 50] {
        first_argument[0] + second_argument
    }
    // The text [weight = 9] in a comment is not an annotation.
    spec fun commented(x: num): num /* [weight = 9] */ [weight = 7] {
        x
    }

    spec fun uninterpreted(x: num): num [weight = 3];

    spec lemma sum_nonneg(v: vector<u64> , n: num) {
        requires 0 <= n && n <= len(v);
        ensures spec_sum(v, n) >= 0;
    } proof {
        if (n > 0) {
            apply sum_nonneg(v, n - 1);
        }
    }
}
