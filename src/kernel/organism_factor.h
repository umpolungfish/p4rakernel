#pragma once
#include "kernel/inclosure.h"
#include <dlfcn.h>

namespace lean {
class organism_factor_task : public organism_task {
    void * m_library = nullptr;
    void * m_body = nullptr;
    using create_fn = void * (*)(char const *);
    using destroy_fn = void (*)(void *);
    using advance_fn = int (*)(void *, size_t);
    using reentry_fn = int (*)(void *, unsigned, unsigned, unsigned, unsigned);
    using closed_fn = bool (*)(void *);
    using snapshot_fn = char const * (*)(void *);
    using source_fn = int (*)(void *, size_t);
    using count_fn = size_t (*)(void *);
    destroy_fn m_destroy;
    advance_fn m_advance;
    reentry_fn m_reenter;
    sixteen3 m_reentry;
    closed_fn m_closed;
    closed_fn m_should_yield;
    count_fn m_operation_count;
    snapshot_fn m_snapshot;
    snapshot_fn m_observation;
    source_fn m_source;
    source_fn m_state;
    size_t m_components;
    template<typename T> T symbol(char const * name) {
        auto address = dlsym(m_library, name);
        if (!address) throw std::runtime_error(std::string("factor bridge symbol missing: ")+name);
        return reinterpret_cast<T>(address);
    }
public:
    organism_factor_task(std::string const & source, std::string const & library) {
        m_library = dlopen(library.c_str(), RTLD_NOW | RTLD_LOCAL);
        if (!m_library) throw std::runtime_error(dlerror());
        try {
            m_destroy=symbol<destroy_fn>("organism_factor_destroy");
            m_advance=symbol<advance_fn>("organism_factor_advance");
            m_reenter=symbol<reentry_fn>("organism_factor_reentry");
            m_closed=symbol<closed_fn>("organism_factor_closed");
            m_should_yield=symbol<closed_fn>("organism_factor_should_yield");
            m_operation_count=symbol<count_fn>("organism_factor_operation_count");
            m_snapshot=symbol<snapshot_fn>("organism_factor_snapshot");
            m_observation=symbol<snapshot_fn>("organism_factor_observation");
            m_source=symbol<source_fn>("organism_factor_source_token");
            m_state=symbol<source_fn>("organism_factor_state_token");
            m_components=symbol<size_t(*)()>("organism_factor_components")();
            m_body=symbol<create_fn>("organism_factor_create")(source.c_str());
            if (!m_body) throw std::runtime_error("native N-only factor preparation rejected; see its retained diagnostic");
        } catch (...) { dlclose(m_library); throw; }
    }
    ~organism_factor_task() override { if(m_body)m_destroy(m_body);dlclose(m_library); }
    size_t components() const override {return m_components;}
    bool closed() const override {return m_closed(m_body);}
    bool should_yield() const override {return m_should_yield(m_body);}
    std::string snapshot() const override {return m_snapshot(m_body);}
    std::vector<unsigned> source_tokens() const override {
        std::vector<unsigned> result;
        for(size_t i=0;;++i){int token=m_source(m_body,i);if(token<0)break;result.push_back(token);}
        return result;
    }
    organism_task_observation advance(size_t component) override {
        if (should_yield()) return {component,sixteen3_none(),false,"null",{},false};
        auto permutation=m_reentry.reentry_permutation();
        bool returning=m_reentry==sixteen3_all();
        auto next=returning ? m_reentry.conflation() : inclosure::wind(m_reentry);
        int gate=m_reenter(m_body,m_reentry.mask(),permutation.mask(),next.mask(),returning ? 2u : 1u);
        if(gate<0)throw std::runtime_error("native factor re-entry transport failed");
        if(gate==0)m_reentry=next;
        auto count=m_operation_count(m_body);
        int result=m_advance(m_body,component);
        if(result<0 || result>15)throw std::runtime_error("native factor operation returned invalid evidence");
        if(m_operation_count(m_body)==count) return {component,sixteen3_none(),false,"null",{},false};
        std::vector<unsigned> context;
        for(size_t i=0;;++i){int token=m_state(m_body,i);if(token<0)break;context.push_back(token);}
        return {component,sixteen3::from_mask(result),closed(),m_observation(m_body),std::move(context)};
    }
};
}
