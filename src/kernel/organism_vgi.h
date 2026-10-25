#pragma once
#include "kernel/inclosure.h"
#include <dlfcn.h>
#include <link.h>
#include <cmath>
#include <iomanip>
#include <sstream>

namespace lean {
/** Native P(FOUR) ↔ VGI Reg16_3 transport. N→f, T→t, F→F, B→T.
    This is a coordinate transport, with an explicit inverse at readout. */
inline unsigned organism_vgi_transport(unsigned x) {
    return ((x & 1) << 3) | ((x & 2) << 1) | ((x & 4) >> 1) | ((x & 8) >> 3);
}

class vgi_organism_learner : public organism_learner {
    void * m_library;
    size_t m_parameters, m_dimension;
    using reset_fn = void (*)();
    using token_fn = long (*)(long, long);
    using update_fn = long (*)(long, long, long, long, long, long);
    using pair_fn = double (*)(long, long);
    using scalar_fn = double (*)(long);
    token_fn m_token;
    update_fn m_update;
    pair_fn m_first, m_memory, m_optimizer;
    scalar_fn m_parameter;
    reset_fn m_context_begin, m_context_end;
    bool m_learning;
    template<typename T> T symbol(char const * name) {
        auto address = dlsym(m_library, name);
        if (!address) throw std::runtime_error(std::string("VGI symbol missing: ") + name);
        return reinterpret_cast<T>(address);
    }
    std::array<double, 4> rails() const {
        std::array<double, 4> result;
        for (unsigned k = 0; k < 4; ++k) {
            result[k] = m_first(k % 2, 259 + k / 2);
            if (!std::isfinite(result[k])) throw std::runtime_error("nonfinite VGI evidence rail");
        }
        return result;
    }
    static sixteen3 read(std::array<double, 4> const & rails) {
        unsigned result = 0;
        for (unsigned k = 0; k < 4; ++k) if (rails[k] > 0) result |= 1u << k;
        return sixteen3::from_mask(organism_vgi_transport(result));
    }
public:
    explicit vgi_organism_learner(std::string const & path, bool learning = true)
        : m_library(nullptr), m_parameters(0), m_dimension(0), m_learning(learning) {
        // The exported VGI runtime owns static banks. A distinct loader
        // namespace gives each organism its own weights, moments and memory.
        m_library = dlmopen(LM_ID_NEWLM, path.c_str(), RTLD_NOW | RTLD_LOCAL);
        if (!m_library) throw std::runtime_error(dlerror());
        try {
            m_token = symbol<token_fn>("vgi_retained_token");
            m_update = symbol<update_fn>("vgi_retained_update");
            m_first = symbol<pair_fn>("vgi_retained_first");
            m_memory = symbol<pair_fn>("vgi_retained_memory");
            m_optimizer = symbol<pair_fn>("vgi_optimizer_observe");
            m_parameter = symbol<scalar_fn>("vgi_full_parameter");
            m_context_begin = symbol<reset_fn>("vgi_organism_context_begin");
            m_context_end = symbol<reset_fn>("vgi_organism_context_end");
            auto config = symbol<long (*)(long)>("vgi_organism_config");
            if (config(0) <= 0 || config(1) <= 0 || config(2) < 282)
                throw std::runtime_error("incompatible VGI organism configuration");
            m_parameters = static_cast<size_t>(config(0));
            m_dimension = static_cast<size_t>(config(1));
            symbol<reset_fn>("vgi_retained_reset")();
        } catch (...) { dlclose(m_library); throw; }
    }
    ~vgi_organism_learner() override { dlclose(m_library); }
    void bind_source(std::vector<unsigned> const & tokens) override {
        std::vector<long> query{256, 83};
        for (auto token : tokens) {
            if (token > 15) throw std::invalid_argument("source context token is not a numeral nibble");
            query.push_back(266 + token);
        }
        query.push_back(257);
        for (size_t i = 0; i < query.size(); ++i)
            if (m_token(i, query[i]) < 0) throw std::runtime_error("VGI source context rejected");
        m_context_begin();
        if (m_update(query.size(), 0, 2, 0, 0, 1) < 0)
            throw std::runtime_error("VGI source preparation failed");
        m_context_end();
    }
    void observe_task(unsigned component, sixteen3 value) override {
        long query[] = {256,84,static_cast<long>(component),266+organism_vgi_transport(value.mask()),0,1,0,257};
        for (unsigned i=0;i<8;++i)
            if (m_token(i,query[i])<0) throw std::runtime_error("VGI task observation rejected");
        m_context_begin();
        if (m_update(8,0,2,organism_vgi_transport(value.mask()),m_learning?1:0,1)<0)
            throw std::runtime_error("VGI task learning failed");
        m_context_end();
    }
    organism_neural_observation act(organism_op op, sixteen3 input, sixteen3 operand,
                                    sixteen3 expected) override {
        // Marker K (75) distinguishes kernel-operation queries from VGI's
        // existing G (71) graph-port queries. Ordinal identity is not assumed.
        long query[] = {256, 75, static_cast<long>(op),
                        266 + organism_vgi_transport(input.mask()),
                        266 + organism_vgi_transport(operand.mask()), 1, 0, 257};
        for (unsigned i = 0; i < 8; ++i)
            if (m_token(i, query[i]) < 0) throw std::runtime_error("VGI query rejected");
        long target = organism_vgi_transport(expected.mask());
        m_context_begin();
        if (m_update(8, 0, 2, target, 0, 1) < 0) throw std::runtime_error("VGI observation failed");
        auto before = rails();
        double clock_before = m_optimizer(0, 0);
        if (m_update(8, 0, 2, target, m_learning ? 1 : 0, 1) < 0) throw std::runtime_error("VGI learning failed");
        if (m_update(8, 0, 2, target, 0, 1) < 0) throw std::runtime_error("VGI readout failed");
        auto after = rails();
        m_context_end();
        std::array<organism_evidence, 4> membership;
        auto proposal = read(after);
        for (unsigned bit = 0; bit < 4; ++bit)
            membership[bit] = witnessed((proposal.mask() >> bit) & 1).join(
                               witnessed((expected.mask() >> bit) & 1));
        return {op, input, operand, expected, read(before), proposal, before, after,
                clock_before, m_optimizer(0, 0), membership};
    }
    std::string snapshot() const override {
        std::ostringstream s;
        s << std::setprecision(17) << "{\"backend\":\"VGI-native-retained\",\"optimizer_clock\":" << m_optimizer(0, 0);
        for (unsigned kind = 0; kind < 3; ++kind) {
            s << (kind == 0 ? ",\"parameters\":[" : kind == 1 ? ",\"adam_m\":[" : ",\"adam_v\":[");
            for (size_t i = 0; i < m_parameters; ++i) {
                if (i) s << ",";
                s << (kind == 0 ? m_parameter(i) : m_optimizer(kind, i));
            }
            s << "]";
        }
        s << ",\"adam_powers\":[" << m_optimizer(3, 0) << "," << m_optimizer(3, 1) << "],\"memory\":[";
        for (unsigned channel = 0; channel < 2; ++channel) {
            if (channel) s << ",";
            s << "[";
            for (size_t i = 0; i < m_dimension; ++i) { if (i) s << ","; s << m_memory(channel, i); }
            s << "]";
        }
        s << "]}";
        return s.str();
    }
};
}
