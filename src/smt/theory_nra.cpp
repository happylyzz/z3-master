/*++
  Copyright (c) 2016 Microsoft Corporation

  Module Name:

  theory_nra.cpp

  Abstract:

  <abstract>

  Author:

  Lev Nachmanson (levnach) 2016-25-3
  Nikolaj Bjorner (nbjorner)

  Revision History:


  --*/
#include "util/stopwatch.h"
#include "math/polynomial/algebraic_numbers.h"
#include "math/polynomial/polynomial.h"
#include "util/nat_set.h"
#include "util/optional.h"
#include "util/inf_rational.h"
#include "util/cancel_eh.h"
#include "util/scoped_timer.h"
#include "util/nat_set.h"
#include "ast/ast_pp.h"
#include "model/numeral_factory.h"
#include "smt/smt_theory.h"
#include "smt/smt_context.h"
#include "smt/theory_nra.h"
#include "smt/smt_model_generator.h"
#include "smt/arith_eq_adapter.h"
#include "util/nat_set.h"
#include "tactic/generic_model_converter.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "util/cancel_eh.h"
#include "util/scoped_timer.h"


// not used? lra
#include "math/lp/lp_solver.h"
#include "math/lp/lp_primal_simplex.h"
#include "math/lp/lp_dual_simplex.h"
#include "math/lp/indexed_value.h"
#include "math/lp/lar_solver.h"
#include "math/lp/nla_solver.h"
#include "math/lp/lp_types.h"
#include "math/lp/lp_api.h"
// nra
#include "nlsat/nlsat_solver.h"
#include "nlsat/nlsat_types.h"
#include "nlsat/nlsat_assignment.h"

#include "math/lp/nra_solver.h"
#include "util/map.h"
#include "math/lp/u_set.h"
#include "math/lp/nla_core.h"
#include "math/lp/numeric_pair.h"
#include "smt/params/smt_params_helper.hpp"


#include "util/vector.h"
#include <utility>
#include "util/debug.h"
#include "util/buffer.h"
#include <unordered_map>
#include <unordered_set>
#include <string>
#include <algorithm>
#include <stack>
#include <functional>
#include "math/lp/lar_constraints.h"
#include "math/lp/lar_core_solver.h"
#include "math/lp/numeric_pair.h"
#include "math/lp/scaler.h"
#include "math/lp/lp_primal_core_solver.h"
#include "math/lp/random_updater.h"
#include "util/stacked_value.h"
#include "math/lp/stacked_vector.h"
#include "math/lp/implied_bound.h"
#include "math/lp/bound_analyzer_on_row.h"
#include "math/lp/conversion_helper.h"
#include "math/lp/int_solver.h"
#include "math/lp/lp_bound_propagator.h"

#include "nlsat/nlsat_solver.h"
#include "nlsat/nlsat_clause.h"
#include "nlsat/nlsat_assignment.h"
#include "nlsat/nlsat_justification.h"
#include "nlsat/nlsat_evaluator.h"
#include "nlsat/nlsat_explain.h"
#include "nlsat/nlsat_params.hpp"

#include "math/lp/nla_core.h"


typedef lp::var_index lpvar;


namespace smt {

    typedef lp_api::bound<literal> api_bound;

    typedef ptr_vector<api_bound> lp_bounds;
    
    typedef nla::mon_eq mon_eq;

    typedef nla::variable_map_type variable_map_type;

class theory_nra::imp {        

    lp::lar_solver&           s;
    reslimit&                 m_limit;  
    params_ref                m_params; 
    u_map<polynomial::var>    m_lp2nl;  // map from lar_solver variables to nlsat::solver variables        
    lp::u_set                 m_term_set;
    scoped_ptr<nlsat::solver> m_nlsat;
    scoped_ptr<scoped_anum>   m_zero;
    mutable variable_map_type m_variable_values; // current model        
    nla::core&                m_nla_core;    
    imp(lp::lar_solver& s, reslimit& lim, params_ref const& p, nla::core& nla_core): 
        s(s), 
        m_limit(lim),
        m_params(p),
        m_nla_core(nla_core) {}

    bool need_check() {
        return m_nla_core.m_to_refine.size() != 0;
    }

public:
    /**
       \brief one-shot nlsat check.
       A one shot checker is the least functionality that can 
       enable non-linear reasoning. 
       In addition to checking satisfiability we would also need
       to identify equalities in the model that should be assumed
       with the remaining solver.
           
       TBD: use partial model from lra_solver to prime the state of nlsat_solver.
       TBD: explore more incremental ways of applying nlsat (using assumptions)
    */


    ast_manager&                 m;
    arith_util                   a;
	scoped_ptr<nla::solver>  m_nla;
	lp::impq prev_value;
       lp::impq opt_val;
	vector<lp_bounds>      m_bounds;
	lp::int_solver *m_int_solver = nullptr;
	lp::lar_core_solver    m_mpq_lar_core_solver;


    /*lbool check() {        
        SASSERT(need_check());
        m_zero = nullptr;
        m_nlsat = alloc(nlsat::solver, m_limit, m_params, false);
        m_zero = alloc(scoped_anum, am());
        m_term_set.clear();
        m_lp2nl.reset();
        vector<nlsat::assumption, false> core;

        // add linear inequalities from lra_solver
        for (lp::constraint_index ci : s.constraints().indices()) {
            add_constraint(ci);
        }

        // add polynomial definitions.
        for (auto const& m : m_nla_core.emons()) 
             add_monic_eq(m);
        for (unsigned i : m_term_set) 
            add_term(i);
        // TBD: add variable bounds?

        lbool r = l_undef;
        try {
            r = m_nlsat->check(); 
        }
        catch (z3_exception&) {
            if (m_limit.is_canceled()) {
                r = l_undef;
            }
            else {
                throw;
            }
        }
        TRACE("nra", 
              m_nlsat->display(tout << r << "\n");
              display(tout); 
              for (auto kv : m_lp2nl) 
                  tout << "j" << kv.m_key << " := x" << kv.m_value << "\n";
              );
        switch (r) {
        case l_true: 
            m_nla_core.set_use_nra_model(true);
            break;
        case l_false: {
            lp::explanation ex;
            m_nlsat->get_core(core);
            for (auto c : core) {
                unsigned idx = static_cast<unsigned>(static_cast<imp*>(c) - this);
                ex.push_back(idx);
                TRACE("arith", tout << "ex: " << idx << "\n";);
            }
            nla::new_lemma lemma(m_nla_core, __FUNCTION__);
            lemma &= ex;
            m_nla_core.set_use_nra_model(true);
            break;
        }
        case l_undef:
            break;
        }            
        return r;
    }   */             


    lp::lar_solver& lp(){ return *theory_lra::imp::m_solver.get(); }
    const lp::lar_solver& lp() const { return *theory_lra::imp::m_solver.get(); }    


    void add_monic_eq(mon_eq const& m) {
        polynomial::manager& pm = m_nlsat->pm();
        svector<polynomial::var> vars;
        for (auto v : m.vars()) {
            vars.push_back(lp2nl(v));
        }
        polynomial::monomial_ref m1(pm.mk_monomial(vars.size(), vars.data()), pm);
        polynomial::monomial_ref m2(pm.mk_monomial(lp2nl(m.var()), 1), pm);
        polynomial::monomial * mls[2] = { m1, m2 };
        polynomial::scoped_numeral_vector coeffs(pm.m());
        coeffs.push_back(mpz(1));
        coeffs.push_back(mpz(-1));
        polynomial::polynomial_ref p(pm.mk_polynomial(2, coeffs.data(), mls),  pm);
        polynomial::polynomial* ps[1] = { p };
        bool even[1] = { false };
        nlsat::literal lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::EQ, 1, ps, even);
        m_nlsat->mk_clause(1, &lit, nullptr);
    }

    void add_constraint(unsigned idx) {
        auto& c = s.constraints()[idx];
        auto& pm = m_nlsat->pm();
        auto k = c.kind();
        auto rhs = c.rhs();
        auto lhs = c.coeffs();
        auto sz = lhs.size();
        svector<polynomial::var> vars;
        rational den = denominator(rhs);
        for (auto kv : lhs) {
            vars.push_back(lp2nl(kv.second));
            den = lcm(den, denominator(kv.first));
        }
        vector<rational> coeffs;
        for (auto kv : lhs) {
            coeffs.push_back(den * kv.first);
        }
        rhs *= den;
        polynomial::polynomial_ref p(pm.mk_linear(sz, coeffs.data(), vars.data(), -rhs), pm);
        polynomial::polynomial* ps[1] = { p };
        bool is_even[1] = { false };
        nlsat::literal lit;
        nlsat::assumption a = this + idx;
        switch (k) {
        case lp::lconstraint_kind::LE:
            lit = ~m_nlsat->mk_ineq_literal(nlsat::atom::kind::GT, 1, ps, is_even);
            break;
        case lp::lconstraint_kind::GE:
            lit = ~m_nlsat->mk_ineq_literal(nlsat::atom::kind::LT, 1, ps, is_even);
            break;
        case lp::lconstraint_kind::LT:
            lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::LT, 1, ps, is_even);
            break;
        case lp::lconstraint_kind::GT:
            lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::GT, 1, ps, is_even);
            break;
        case lp::lconstraint_kind::EQ:
            lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::EQ, 1, ps, is_even);                
            break;
        default:
            lp_assert(false); // unreachable
        }
        m_nlsat->mk_clause(1, &lit, a);
    }





    /*lbool check(vector<dd::pdd> const& eqs) {
        m_zero = nullptr;
        m_nlsat = alloc(nlsat::solver, m_limit, m_params, false);
        m_zero = alloc(scoped_anum, am());
        m_lp2nl.reset();
        m_term_set.clear();
        for (auto const& eq : eqs)
            add_eq(eq);
        for (auto const& [v, w] : m_lp2nl) {
            auto& ls = m_nla_core.m_lar_solver;
            if (ls.column_has_lower_bound(v))
                add_lb(ls.get_lower_bound(v), w);
            if (ls.column_has_upper_bound(v))
                add_ub(ls.get_upper_bound(v), w);
        }

        lbool r = l_undef;
        try {
            r = m_nlsat->check(); 
        }
        catch (z3_exception&) {
            if (m_limit.is_canceled()) {
                r = l_undef;
            }
            else {
                throw;
            }
        }

        IF_VERBOSE(0, verbose_stream() << "check-nra " << r << "\n";
                   m_nlsat->display(verbose_stream());
                   for (auto const& [v, w] : m_lp2nl) {
                       auto& ls = m_nla_core.m_lar_solver;
                       if (ls.column_has_lower_bound(v))
                           verbose_stream() << w << " >= " << ls.get_lower_bound(v) << "\n";
                       if (ls.column_has_upper_bound(v))
                           verbose_stream() << w << " <= " << ls.get_upper_bound(v) << "\n";
                   });                   
        

        return r;
    }*/

    void add_eq(dd::pdd const& eq) {
        dd::pdd normeq = eq;
        rational lc(1);
        for (auto const& [c, m] : eq) 
            lc = lcm(denominator(c), lc);
        if (lc != 1)
            normeq *= lc;
        polynomial::manager& pm = m_nlsat->pm();
        polynomial::polynomial_ref p(pdd2polynomial(normeq), pm);
        bool is_even[1] = { false };
        polynomial::polynomial* ps[1] = { p };               
        nlsat::literal lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::EQ, 1, ps, is_even);                
        m_nlsat->mk_clause(1, &lit, nullptr);
    }

    void add_lb(lp::impq const& b, unsigned w) {
        add_bound(b.x, w, b.y <= 0, b.y > 0 ? nlsat::atom::kind::GT : nlsat::atom::kind::LT);
    }
    void add_ub(lp::impq const& b, unsigned w) {
        add_bound(b.x, w, b.y >= 0, b.y < 0 ? nlsat::atom::kind::LT : nlsat::atom::kind::GT);
    }

    // w - bound < 0
    // w - bound > 0
    void add_bound(lp::mpq const& bound, unsigned w, bool neg, nlsat::atom::kind k) {
        polynomial::manager& pm = m_nlsat->pm();
        polynomial::polynomial_ref p1(pm.mk_polynomial(w), pm);
        polynomial::polynomial_ref p2(pm.mk_const(bound), pm);
        polynomial::polynomial_ref p(pm.sub(p1, p2), pm);
        polynomial::polynomial* ps[1] = { p };
        bool is_even[1] = { false };
        nlsat::literal lit = m_nlsat->mk_ineq_literal(k, 1, ps, is_even);
        if (neg)
            lit.neg();
        m_nlsat->mk_clause(1, &lit, nullptr);
    }
    
    polynomial::polynomial* pdd2polynomial(dd::pdd const& p) {
        polynomial::manager& pm = m_nlsat->pm();
        if (p.is_val()) 
            return pm.mk_const(p.val());
        polynomial::polynomial_ref lo(pdd2polynomial(p.lo()), pm);
        polynomial::polynomial_ref hi(pdd2polynomial(p.hi()), pm);
        unsigned w, v = p.var();
        if (!m_lp2nl.find(v, w)) {
            w = m_nlsat->mk_var(false);
            m_lp2nl.insert(v, w);
        }
        polynomial::polynomial_ref vp(pm.mk_polynomial(w, 1), pm);
        return pm.add(lo, pm.mul(vp, hi));
    }

    bool is_int(lp::var_index v) {
        return s.var_is_int(v);
    }


    polynomial::var lp2nl(lp::var_index v) {
        polynomial::var r;
        if (!m_lp2nl.find(v, r)) {
            r = m_nlsat->mk_var(is_int(v));
            m_lp2nl.insert(v, r);
            if (!m_term_set.contains(v) && s.column_corresponds_to_term(v)) {
                if (v >= m_term_set.data_size())
                    m_term_set.resize(v + 1);
                m_term_set.insert(v);
            }
        }
        return r;
    }
    //
    void add_term(unsigned term_column) {
        lp::tv ti = lp::tv::raw(s.column_to_reported_index(term_column));
        const lp::lar_term& t = s.get_term(ti); 
        //  code that creates a polynomial equality between the linear coefficients and
        // variable representing the term.
        svector<polynomial::var> vars;
        rational den(1);
        for (lp::lar_term::ival kv : t) {
            vars.push_back(lp2nl(kv.column().index()));
            den = lcm(den, denominator(kv.coeff()));
        }
        vars.push_back(lp2nl(term_column));
        
        vector<rational> coeffs;
        for (auto kv : t) {
            coeffs.push_back(den * kv.coeff());
        }
        coeffs.push_back(-den);
        polynomial::manager& pm = m_nlsat->pm();
        polynomial::polynomial_ref p(pm.mk_linear(coeffs.size(), coeffs.data(), vars.data(), rational(0)), pm);
        polynomial::polynomial* ps[1] = { p };
        bool is_even[1] = { false };
        nlsat::literal lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::EQ, 1, ps, is_even);                
        m_nlsat->mk_clause(1, &lit, nullptr);
    }
//参照check()写（添加bound,获取当前变量的不可满足区间（给nlsat实现），check()）


    nlsat::anum const& value(lp::var_index v) const {
        polynomial::var pv;
        if (m_lp2nl.find(v, pv))
            return m_nlsat->value(pv);
        else
            return *m_zero;
    }

    nlsat::anum_manager& am() {
        return m_nlsat->am();
    }

    void updt_params(params_ref& p) {
        m_params.append(p);
    }


    std::ostream& display(std::ostream& out) const {
        for (auto m : m_nla_core.emons()) {
            out << "j" << m.var() << " = ";
            for (auto v : m.vars()) {
                out << "j" << v << " ";
            }
            out << "\n";
        }
        return out;
    }
       


    theory_nra::inf_eps value(theory_var v) {
        lp::impq ival = theory_lra::get_ivalue(v);
        return inf_eps(rational(0), inf_rational(ival.x, ival.y));
    }

    lpvar register_theory_var_in_lar_solver(theory_var v) {
        lpvar lpv = theory_lra::imp::lp().external_to_local(v);
        if (lpv != lp::null_lpvar)
            return lpv;
        return theory_lra::imp::lp().add_var(v, is_int(v));
    }
    /*theory_var internalize_def(app* term, theory_lra::imp::scoped_internalize_state& st) {
        TRACE("arith", tout << expr_ref(term, m) << "\n";);
        if (ctx().e_internalized(term)) {
            IF_VERBOSE(0, verbose_stream() << "repeated term\n";);
            return mk_var(term);
        }
        linearize_term(term, st);
        if (is_unit_var(st)) {
            return st.vars()[0];
        }
        else {
            theory_var v = mk_var(term);
            SASSERT(null_theory_var != v);
            st.coeffs().resize(st.vars().size() + 1);
            st.coeffs()[st.vars().size()] = rational::minus_one();
            st.vars().push_back(v);
            return v;
        }
    }


    theory_var internalize_def(app* term) {
        theory_lra::imp::scoped_internalize_state st(*this);
        linearize_term(term, st);
        return theory_lra::imp::internalize_linearized_def(term, st);
    }*/

    void add_var_bound()//直接调用nra_solver的add_constraint，把bound对应的index添加进去，需要多次调用nlsat。只需要添加指定的变量的边界
    {
        for(unsigned i = 0 ; i < m_bounds.size() ; i++)
        {
            for(unsigned j = 0; j < 2 ; j++)
            {
                //auto& c = m_bounds[i].m_constraints[j];
		auto& c = m_bounds[i].contains[j];
                auto& pm = m_nlsat->pm();
                auto k = c.kind();
                auto rhs = c.rhs();
                auto lhs = c.coeffs();
                auto sz = lhs.size();
                svector<polynomial::var> vars;
                rational den = denominator(rhs);
                for (auto kv : lhs) {
                    vars.push_back(lp2nl(kv.second));
                    den = lcm(den, denominator(kv.first));
                }
                vector<rational> coeffs;
                for (auto kv : lhs) {
                    coeffs.push_back(den * kv.first);
                }
                rhs *= den;
                polynomial::polynomial_ref p(pm.mk_linear(sz, coeffs.data(), vars.data(), -rhs), pm);
                polynomial::polynomial* ps[1] = { p };
                bool is_even[1] = { false };
                nlsat::literal lit;
                nlsat::assumption a = this + j;
                switch (k) {
                case lp::lconstraint_kind::LE:
                    lit = ~m_nlsat->mk_ineq_literal(nlsat::atom::kind::GT, 1, ps, is_even);
                    break;
                case lp::lconstraint_kind::GE:
                    lit = ~m_nlsat->mk_ineq_literal(nlsat::atom::kind::LT, 1, ps, is_even);
                    break;
                case lp::lconstraint_kind::LT:
                    lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::LT, 1, ps, is_even);
                    break;
                case lp::lconstraint_kind::GT:
                    lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::GT, 1, ps, is_even);
                    break;
                case lp::lconstraint_kind::EQ:
                    lit = m_nlsat->mk_ineq_literal(nlsat::atom::kind::EQ, 1, ps, is_even);                
                    break;
                default:
                    lp_assert(false); // unreachable
                }
                m_nlsat->mk_clause(1, &lit, a);
            }

        }
    }


lp::lp_status maximize_term(unsigned j_or_term,  lp::impq& term_max) {
        TRACE("lar_solver", lp::lar_solver::print_values(tout););
        for (lp::constraint_index ci : s.constraints().indices()) {
            add_constraint(ci);
        }

        // add polynomial definitions.
        for (auto const& m : m_nla_core.emons()) 
             add_monic_eq(m);
        for (unsigned i : m_term_set) 
            add_term(i);
        // TBD: add variable bounds?
        add_var_bound();
        /*for(unsigned i = 0 ; i < m_bounds.size() ; i++)
        {
            api_bound* b = mk_var_bound(bv, v, k, r);
            m_bounds[v].push_back(b);
            updt_unassigned_bounds(v, +1);
            m_bounds_trail.push_back(v);
            m_bool_var2bound.insert(bv, b);
        }*/



        nra::solver::check();
        lp::lar_term term = lp::lar_solver::get_term_to_maximize(j_or_term);
        if (term.is_empty()) {
            return lp::lp_status::UNBOUNDED;
        }

        auto backup = m_mpq_lar_core_solver.m_r_x;
        if (m_mpq_lar_core_solver.m_r_solver.calc_current_x_is_feasible_include_non_basis()) {
            prev_value = term.apply(m_mpq_lar_core_solver.m_r_x);
        }
        else {
            m_mpq_lar_core_solver.m_r_solver.m_look_for_feasible_solution_only = false;
            if (lp::lar_solver::solve() != lp::lp_status::OPTIMAL)
                return lp::lp_status::UNBOUNDED;
        }

        m_mpq_lar_core_solver.m_r_solver.m_look_for_feasible_solution_only = false;
        if (!lp::lar_solver::maximize_term_on_corrected_r_solver(term, term_max)) {
            m_mpq_lar_core_solver.m_r_x = backup;
            return lp::lp_status::UNBOUNDED;
        }

        //impq opt_val = term_max;
	opt_val = term_max;
        bool change = false;
        for (unsigned j = 0; j < m_mpq_lar_core_solver.m_r_x.size(); j++) {
            if (!lp::lar_solver::column_is_int(j))
                continue;
            if (lp::lar_solver::column_value_is_integer(j))
                continue;
            if (m_int_solver->is_base(j)) {
                if (!lp::lar_solver::remove_from_basis(j)) { // consider a special version of remove_from_basis that would not remove inf_int columns
                    m_mpq_lar_core_solver.m_r_x = backup;
                    term_max = prev_value;
                    return lp::lp_status::FEASIBLE; // it should not happen
                }
            }
            m_int_solver->patch_nbasic_column(j);
            if (!lp::lar_solver::column_value_is_integer(j)) {
                term_max = prev_value;
                m_mpq_lar_core_solver.m_r_x = backup;
                return lp::lp_status::FEASIBLE;
            }
            change = true;
        }
        if (change) {
            term_max = term.apply(m_mpq_lar_core_solver.m_r_x);
        }
        if (term_max < prev_value) {
            term_max = prev_value;
            m_mpq_lar_core_solver.m_r_x = backup;
        }
        TRACE("lar_solver", lp::lar_solver::print_values(tout););
        if (term_max == opt_val) {
            lp::lp_solver::set_status(lp::lp_status::OPTIMAL);
            return lp::lp_status::OPTIMAL;
        }
        return lp::lp_status::FEASIBLE;
    }



//把注释的代码git到仓库中
    theory_nra::inf_eps maximize(theory_var v, expr_ref& blocker, bool& has_shared) {
        // TODO
        lp::impq term_max;
        lp::lp_status st;
        lpvar vi = 0;
        if (theory_lra::has_int()) {
            lp().backup_x();//把lp的意义弄明白，看是不是可以删掉
        }
        if (!theory_lra::is_registered_var(v)) {
            TRACE("arith", tout << "cannot get bound for v" << v << "\n";);
            st = lp::lp_status::UNBOUNDED;
        }
        else if (!m.limit().inc()) {
            st = lp::lp_status::UNBOUNDED;
        }
        else {
            if (!lp().is_feasible() || lp().has_changed_columns())
                smt::theory_lra::make_feasible();
            
            vi = theory_lra::get_lpvar(v);
            



            st = lp::lar_solver::maximize_term(vi, term_max);//修改成求nra的算法



            if (theory_lra::has_int() && lp().has_inf_int()) {
                st = lp::lp_status::FEASIBLE;
                lp().restore_x();
            }
            if (m_nla && (st == lp::lp_status::OPTIMAL || st == lp::lp_status::UNBOUNDED)) {
                st = lp::lp_status::FEASIBLE;
                lp().restore_x();
            }                
        }
        switch (st) {
        case lp::lp_status::OPTIMAL: {
            theory_lra::init_variable_values();
            TRACE("arith", display(tout << st << " v" << v << " vi: " << vi << "\n"););
            auto val = value(v);
            blocker = mk_gt(v);
            return val;
        }
        case lp::lp_status::FEASIBLE: {
            auto val = value(v);
            TRACE("arith", display(tout << st << " v" << v << " vi: " << vi << "\n"););
            blocker = mk_gt(v);
            return val;
        }
        default:
            SASSERT(st == lp::lp_status::UNBOUNDED);
            TRACE("arith", display(tout << st << " v" << v << " vi: " << vi << "\n"););
            has_shared = false;
            blocker = m.mk_false();
            return inf_eps(rational::one(), inf_rational());
        }
    }


    expr_ref mk_gt(theory_var v) {
        lp::impq val = theory_lra::get_ivalue(v);
        expr* obj = get_enode(v)->get_expr();
        rational r = val.x;
        expr_ref e(m);
        if (a.is_int(obj->get_sort())) {
            if (r.is_int()) 
                r += rational::one();
            else 
                r = ceil(r);
            e = a.mk_numeral(r, obj->get_sort());
            e = a.mk_ge(obj, e);
        }
        else {
            e = a.mk_numeral(r, obj->get_sort());
            if (val.y.is_neg()) 
                e = a.mk_ge(obj, e);
            else 
                e = a.mk_gt(obj, e);
        }
        TRACE("opt", tout << "v" << v << " " << val << " " << r << " " << e << "\n";);
        return e;
    }

    /*theory_var add_objective(app* term) {
        TRACE("opt", tout << expr_ref(term, m) << "\n";);
        theory_var v = theory_lra::internalize_def(term);
        register_theory_var_in_lar_solver(v);
        return v;
    }*/

    void term2coeffs(lp::lar_term const& term, u_map<rational>& coeffs) {
        term2coeffs(term, coeffs, rational::one());
    }

    void term2coeffs(lp::lar_term const& term, u_map<rational>& coeffs, rational const& coeff) {
        TRACE("arith", lp().print_term(term, tout) << "\n";);
        for (lp::lar_term::ival ti : term) {
            theory_var w;
            auto tv = lp().column2tv(ti.column());
            if (tv.is_term()) {
                lp::lar_term const& term1 = lp().get_term(tv);
                rational coeff2 = coeff * ti.coeff();
                term2coeffs(term1, coeffs, coeff2);
                continue;
            }
            else {
                w = lp().local_to_external(tv.id());
                SASSERT(w >= 0);
                TRACE("arith", tout << (tv.id()) << ": " << w << "\n";);
            }
            rational c0(0);
            coeffs.find(w, c0);
            coeffs.insert(w, c0 + ti.coeff() * coeff);
        }
    }

    app_ref coeffs2app(u_map<rational> const& coeffs, rational const& offset, bool is_int) {
        expr_ref_vector args(m);
        for (auto const& kv : coeffs) {
            theory_var w = kv.m_key;
            expr* o = get_enode(w)->get_expr();
            if (kv.m_value.is_zero()) {
                // continue
            }
            else if (kv.m_value.is_one()) {
                args.push_back(o);
            }
            else {
                args.push_back(a.mk_mul(a.mk_numeral(kv.m_value, is_int), o));                
            }
        }
        if (!offset.is_zero()) {
            args.push_back(a.mk_numeral(offset, is_int));
        }
        switch (args.size()) {
        case 0:
            return app_ref(a.mk_numeral(rational::zero(), is_int), m);
        case 1:
            return app_ref(to_app(args[0].get()), m);
        default:
            return app_ref(a.mk_add(args.size(), args.data()), m);
        }
    }


    app_ref mk_term(lp::lar_term const& term, bool is_int) {     
        u_map<rational> coeffs;
        term2coeffs(term, coeffs);
        return coeffs2app(coeffs, rational::zero(), is_int);
    }

    rational gcd_reduce(u_map<rational>& coeffs) {
        rational g(0);
        for (auto const& kv : coeffs) {
            g = gcd(g, kv.m_value);
        }
        if (g.is_zero())
            return rational::one();
        if (!g.is_one()) {
            for (auto& kv : coeffs) {
                kv.m_value /= g;
            }             
        }
        return g;
    }


     

    /*
     * Facility to put a small box around integer variables used in branch and bounds.
     */

    struct bound_info {
        rational m_offset;
        unsigned m_range;
        bound_info() {}
        bound_info(rational const& o, unsigned r):m_offset(o), m_range(r) {}
    };
    unsigned                  m_bounded_range_idx;  // current size of bounded range.
    literal                   m_bounded_range_lit;  // current bounded range literal
    expr_ref_vector           m_bound_terms; // predicates used for bounds
    expr_ref                  m_bound_predicate;
    
    obj_map<expr, expr*>      m_predicate2term;
    obj_map<expr, bound_info> m_term2bound_info;

    unsigned init_range() const { return 5; }
    unsigned max_range() const { return 20; }
    

    void setup() {
        m_bounded_range_lit = null_literal;
        m_bound_terms.reset();
        m_bound_predicate = nullptr;
        m_predicate2term.reset();
        m_term2bound_info.reset();
    }


};
    
theory_nra::theory_nra(context& ctx):
    theory(ctx, ctx.get_manager().get_family_id("arith")) {
    m_imp = alloc(imp, *this, ctx.get_manager());
}    
theory_nra::~theory_nra() {
    dealloc(m_imp);
}   
theory* theory_nra::mk_fresh(context* new_ctx) {
    return alloc(theory_nra, *new_ctx);
}



void theory_nra::display(std::ostream & out) const {
    m_imp->display(out);
}
theory_nra::inf_eps theory_nra::value(theory_var v) {
    return m_imp->value(v);
}
theory_nra::inf_eps theory_nra::maximize(theory_var v, expr_ref& blocker, bool& has_shared) {
    return m_imp->maximize(v, blocker, has_shared);
}


void theory_nra::setup() {
    m_imp->setup();
}

}


