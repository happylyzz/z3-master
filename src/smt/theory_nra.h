/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    theory_nra.h

Abstract:

    <abstract>

Author:


Revision History:


--*/
#pragma once

#include "smt/theory_opt.h"


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
#include "math/lp/nra_solver.h"
#include "math/lp/lp_types.h"
#include "math/lp/lp_bound_propagator.h"
#include "smt/theory_lra.h"



namespace smt {

//class theory_lra : public theory, public theory_opt {};



    class theory_nra : public theory, public theory_opt {
    public:
        class imp;
    private:
        imp* m_imp;

    public:
        theory_nra(context& ctx);
        ~theory_nra() override;
        theory* mk_fresh(context* new_ctx) override;
        char const* get_name() const override { return "arithmetic"; }

        void init() override;
        
        bool internalize_atom(app * atom, bool gate_ctx) override;
                                                     
        bool internalize_term(app * term) override;

        void internalize_eq_eh(app * atom, bool_var v) override;

        void assign_eh(bool_var v, bool is_true) override;

        lbool get_phase(bool_var v) override;

        void new_eq_eh(theory_var v1, theory_var v2) override;

        bool use_diseqs() const override;

        void new_diseq_eh(theory_var v1, theory_var v2) override;

        void push_scope_eh() override;

        void pop_scope_eh(unsigned num_scopes) override;

        void restart_eh() override;

        void relevant_eh(app* e) override;

        void init_search_eh() override;

        final_check_status final_check_eh() override;

        bool is_shared(theory_var v) const override;
    
        bool can_propagate() override;
        
        void propagate() override;
        
        justification * why_is_diseq(theory_var v1, theory_var v2) override;

        // virtual void flush_eh();

        void reset_eh() override;

        void apply_sort_cnstr(enode * n, sort * s) override;

        void init_model(model_generator & m) override;
        
	void add_var_bound();//add

        model_value_proc * mk_value(enode * n, model_generator & mg) override;

        bool get_value(enode* n, expr_ref& r) override;
        bool include_func_interp(func_decl* f) override;
        bool get_value(enode* n, rational& r);
        bool get_lower(enode* n, expr_ref& r);
        bool get_upper(enode* n, expr_ref& r);
        bool get_lower(enode* n, rational& r, bool& is_strict);
        bool get_upper(enode* n, rational& r, bool& is_strict);
                
        void display(std::ostream & out) const override;
        
        void collect_statistics(::statistics & st) const override;

        void setup() override;

        // optimization
        expr_ref mk_ge(generic_model_converter& fm, theory_var v, inf_rational const& val);
        inf_eps value(theory_var) override;
        inf_eps maximize(theory_var v, expr_ref& blocker, bool& has_shared) override;
        theory_var add_objective(app* term) override;
    };

}

