% ar = access_records
% isDa = is_DoctorA

?- prove((c(pa, ar) and
             (pa says ((hr ratified isDa) -> c(a, ar))) and
             (pa says ((hr says isDa) -> (hr ratified isDa))) and
             (hr says isDa))
            -> c(a, ar)).
