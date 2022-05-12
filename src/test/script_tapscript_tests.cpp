// Copyright (c) 2011-2022 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <hash.h>
#include <script/interpreter.h>
#include <script/script.h>
#include <script/script_error.h>
#include <test/util/setup_common.h>
#include <test/util/transaction_utils.h>
#include <univalue.h>

#include <boost/test/execution_monitor.hpp>
#include <boost/test/unit_test.hpp>

#include <array>
#include <charconv>
#include <cstddef>
#include <iomanip>
#include <iterator>
#include <limits>
#include <ostream>
#include <set>
#include <string_view>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

using namespace std::literals::string_view_literals;

namespace {

typedef std::vector<unsigned char> valtype;

/**
 * Value/Name pair used in data-driven tests
 */
template <typename T>
struct vn_pair
{
    vn_pair(T v, std::string_view n) : value(v), name(n) {}

    const T value;
    const std::string_view name;
};

/**
 * Sequence of value/name pairs used in data-driven tests
 */
template <typename T>
using vn_sequence = std::vector<vn_pair<T>>;

/**
 * Invokes undefined behavior.  See `std::unreachable` in C++23.
 */
[[noreturn]] inline void declare_unreachable()
{
#ifdef _MSC_VER
    __assume(false);
#else
    // Assume all other compilers than MSVC implement this GCC builtin.
    __builtin_unreachable();
#endif
}

/**
 * Outputs to stream as hex
 */
template <typename US>
struct hex
{
    hex(US v) : value(v) {}
    const US value;

    friend std::ostream& operator<<(std::ostream& os, hex hx)
    {
        auto flags = os.flags();
        os << std::setw(2*sizeof(US)) << std::setfill('0') << std::showbase
           << std::hex << +hx.value;
        os.flags(flags);
        return os;
    }
};

/**
 * Representation changer to fill an integral type with a known pattern.
 *
 * Pattern is successive byte values given a starting point.  Endianness doesn't
 * matter.
 */
union FillWithPattern {
    uint256 u256{0};
    uint64_t u64raw[sizeof(uint256)/sizeof(uint64_t)];
    uint32_t u32[sizeof(uint256)/sizeof(uint32_t)];
    int32_t i32[sizeof(uint256)/sizeof(int32_t)];
    uint8_t u8[sizeof(uint256)];

    constexpr FillWithPattern(uint8_t start)
    {
        for (auto it = std::begin(u8); it != std::end(u8); ++it) {
            *it = start++;
        }
    }

    uint64_t u64() const {
        // It is desirable to force high bit off
        return u64raw[0] & static_cast<uint64_t>(std::numeric_limits<int64_t>::max());
    }
};

} // anon namespace

BOOST_FIXTURE_TEST_SUITE(script_tapscript_tests, BasicTestingSetup)

/**
 * Testing EvalScript OP_CHECKSIGADD branch and EvalChecksigTapscript, both in
 * interpreter.cpp, against the BIP342 "Rules for signature opcodes".
 */
BOOST_AUTO_TEST_CASE(eval_checksigadd_basic_checks)
{
    const valtype SIG_64BYTES(64, 0);  // N.B.: Must be () not {}!
    const valtype SIG_65BYTES(65, 0);
    const valtype SIG_EMPTY{};

    const valtype PUBKEY_32BYTES(32, 0);
    const valtype PUBKEY_15BYTES(15, 0);
    const valtype PUBKEY_EMPTY{};

    constexpr int64_t TEST_NUM = 10;

    constexpr int64_t START_VALIDATION_WEIGHT{ 90 };
    constexpr int64_t BIP342_SIGOPS_LIMIT{ 50 };
    constexpr int64_t END_VALIDATION_WEIGHT{ START_VALIDATION_WEIGHT - BIP342_SIGOPS_LIMIT };

    /**
     * For these tests don't need _real_ signature/pubkey validation.  That is
     * tested elsewhere.  So we just _mock_ the signature checker and force it
     * to answer valid/invalid as we wish.
     */

    struct SignatureCheckerMock : public BaseSignatureChecker
    {
        //! Whether this mock always validates, or always fails, the signature/pubkey check.
        enum class VALIDATION { ALWAYS_SUCCEEDS, ALWAYS_FAILS };
        VALIDATION m_kind = VALIDATION::ALWAYS_FAILS;

        //! True _iff_ CheckSchnorrSignature was actually called
        mutable bool m_was_called = false;

        SignatureCheckerMock() {}

        bool CheckSchnorrSignature(Span<const unsigned char> sig,
                                    Span<const unsigned char> pubkey,
                                    SigVersion sigversion,
                                    ScriptExecutionData& execdata,
                                    ScriptError* serror = nullptr) const override
        {
            m_was_called = true;
            switch (m_kind) {
            case VALIDATION::ALWAYS_SUCCEEDS:
                *serror = SCRIPT_ERR_OK;
                return true;
            case VALIDATION::ALWAYS_FAILS:
                *serror = SCRIPT_ERR_SCHNORR_SIG;
                return false;
            }
            declare_unreachable();
        }
    };

    /**
     * A fluent API for running these tests.
     *
     * (Easiest way to understand this class is to look at the actual tests
     * that follow in this function.)
     */
    struct Context
    {
        explicit Context(std::string_view descr) : testDescription(descr) {
            execdata.m_validation_weight_left_init = true;
            execdata.m_validation_weight_left = START_VALIDATION_WEIGHT;
        }

        std::string testDescription;
        SigVersion sigVersion = SigVersion::TAPSCRIPT;
        uint32_t flags = 0;
        CScript script;
        ScriptError err = SCRIPT_ERR_OK;
        std::vector<std::vector<unsigned char>> stack;
        ScriptExecutionData execdata;
        SignatureCheckerMock sigchecker;
        int64_t callerLine = 0;
        bool result = false;

        Context& SetVersion(SigVersion v)
        {
            sigVersion = v;
            return *this;
        }

        Context& SetChecker(SignatureCheckerMock::VALIDATION kind)
        {
            sigchecker.m_kind = kind;
            return *this;
        }

        Context& SetRemainingWeight(int64_t w)
        {
            execdata.m_validation_weight_left = w;
            return *this;
        }

        Context& AddFlags(uint32_t f)
        {
            flags |= f;
            return *this;
        }

        CScript& SetScript()
        {
            return script;
        }

        Context& DoTest(int64_t line)
        {
            callerLine = line;
            result = EvalScript(stack, script,
                                SCRIPT_VERIFY_TAPROOT | flags,
                                sigchecker,
                                sigVersion,
                                execdata,
                                &err);
            return *this;
        }

        Context& CheckCallSucceeded()
        {
            BOOST_CHECK_MESSAGE(result,
                               Descr()
                               << ": EvalScript succeeded, as expected");
            BOOST_CHECK_MESSAGE(err == SCRIPT_ERR_OK,
                                Descr()
                                << ": Error code expected OK, actual was "
                                << ScriptErrorString(err));
            return *this;
        }

        Context& CheckCallFailed(ScriptError expected)
        {
            BOOST_CHECK_MESSAGE(!result,
                               Descr()
                               << ": EvalScript failed, as expected");
            BOOST_CHECK_MESSAGE(err == expected,
                                Descr()
                                << ": Error code expected " << ScriptErrorString(expected)
                                << ", actual was " << ScriptErrorString(err));
            return *this;
        }

        Context& CheckSignatureWasValidated()
        {
            BOOST_CHECK_MESSAGE(sigchecker.m_was_called,
                               Descr()
                               << ": CheckSchnorrSignature was called, as expected");
            return *this;
        }

        Context& CheckSignatureWasNotValidated()
        {
            BOOST_CHECK_MESSAGE(!sigchecker.m_was_called,
                               Descr()
                               << ": CheckSchnorrSignature was not called, as expected");
            return *this;
        }

        Context& CheckRemainingValidationWeight(int64_t expected)
        {
            BOOST_CHECK_MESSAGE(execdata.m_validation_weight_left == expected,
                                Descr()
                                << ": Remaining validation weight expected "
                                << expected << ", actual was "
                                << execdata.m_validation_weight_left);
            return *this;
        }

        Context& CheckStackDepth(std::size_t expected)
        {
            BOOST_CHECK_MESSAGE(stack.size() == expected,
                                Descr()
                                << ": Stack depth expected " << expected
                                << ", actual was " << stack.size());
            return *this;
        }

        Context& CheckTOS(int64_t expected)
        {
            BOOST_CHECK_MESSAGE(!stack.empty(),
                                Descr()
                                << ": Stack expected at least one item, actually was empty");
            const int64_t actual = CScriptNum(stack.at(0), false).GetInt64();
            BOOST_CHECK_MESSAGE(expected == actual,
                                Descr()
                                << ": Top-of-stack expected " << expected
                                << ", actual was " << actual);
            return *this;
        }

    private:
        std::string Descr() {
            std::array<char, 24> sline{0};
            std::string_view svline("");
            // (This seems rather elaborate to avoid locale issues with `std::to_string`. One
            // can't help but think the C++ committee could have provided a nicer wrapper for it.)
            if (auto [ptr,ec] = std::to_chars(sline.data(), sline.data() + sline.size(),
                                            callerLine);
                ec == std::errc())
            {
                svline = std::string_view(sline.data(), ptr - sline.data());
            }

            std::string descr;
            descr.reserve(testDescription.size() + 20);
            descr += testDescription;
            descr += " (@";
            descr += svline;
            descr += ")";
            return descr;
        }
    };

    {
        Context ctx("SigVersion must not be BASE");
        ctx.SetVersion(SigVersion::BASE).SetScript()
            << SIG_64BYTES << CScriptNum(TEST_NUM) << PUBKEY_32BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallFailed(SCRIPT_ERR_BAD_OPCODE)
            .CheckStackDepth(3);
    }

    {
        Context ctx("SigVersion must not be WITNESS_V0");
        ctx.SetVersion(SigVersion::WITNESS_V0).SetScript()
            << SIG_64BYTES << CScriptNum(TEST_NUM) << PUBKEY_32BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallFailed(SCRIPT_ERR_BAD_OPCODE)
            .CheckStackDepth(3);
    }

    {
        Context ctx("Minimum stack height 3 for OP_CHECKSIGADD");
        ctx.SetScript()
            << CScriptNum(TEST_NUM) << PUBKEY_32BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallFailed(SCRIPT_ERR_INVALID_STACK_OPERATION)
            .CheckStackDepth(2);
    }

    {
        Context ctx("`n` (2nd arg) size > 4 must fail");
        // This is probably meant to be a check on the _encoding_ - that it is
        // minimal, but it can also be a check on the _value_.  BIP342 doesn't
        // say which.  Could be both...
        ctx.SetScript()
            << SIG_EMPTY << CScriptNum(10000000000LL) << PUBKEY_32BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            // (IMO this is an _unsatisfactory_ error code to return for a required
            // BIP342 check, but see the `catch` clause in `EvalScript`)
            .CheckCallFailed(SCRIPT_ERR_UNKNOWN_ERROR)
            .CheckStackDepth(3);
    }

    {
        Context ctx("Empty sig + empty pubkey");
        ctx.SetScript()
            << SIG_EMPTY << CScriptNum(TEST_NUM) << PUBKEY_EMPTY << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallFailed(SCRIPT_ERR_PUBKEYTYPE)
            .CheckStackDepth(3);
    }

    {
        Context ctx("Sig + empty pubkey");
        ctx.SetScript()
            << SIG_64BYTES << CScriptNum(TEST_NUM) << PUBKEY_EMPTY << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallFailed(SCRIPT_ERR_PUBKEYTYPE)
            .CheckStackDepth(3);
    }

    {
        Context ctx("Insufficient validation weight remaining");
        ctx.SetRemainingWeight(BIP342_SIGOPS_LIMIT-1)
            .SetScript()
            << SIG_64BYTES << CScriptNum(TEST_NUM) << PUBKEY_32BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallFailed(SCRIPT_ERR_TAPSCRIPT_VALIDATION_WEIGHT)
            .CheckStackDepth(3);
    }

    {
        Context ctx("Empty sig + 32byte pubkey skips validation");
        ctx.SetChecker(SignatureCheckerMock::VALIDATION::ALWAYS_SUCCEEDS)
            .SetScript()
            << SIG_EMPTY << CScriptNum(TEST_NUM) << PUBKEY_32BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallSucceeded()
            .CheckSignatureWasNotValidated()
            .CheckRemainingValidationWeight(START_VALIDATION_WEIGHT)
            .CheckStackDepth(1)
            .CheckTOS(TEST_NUM);
    }

    {
        Context ctx("Empty sig + non32byte pubkey skips validation");
        ctx.SetChecker(SignatureCheckerMock::VALIDATION::ALWAYS_SUCCEEDS)
            .SetScript()
            << SIG_EMPTY << CScriptNum(TEST_NUM) << PUBKEY_15BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallSucceeded()
            .CheckSignatureWasNotValidated()
            .CheckRemainingValidationWeight(START_VALIDATION_WEIGHT)
            .CheckStackDepth(1)
            .CheckTOS(TEST_NUM);
    }

    {
        Context ctx("non32byte pubkey ('unknown pubkey type') _with_ discourage flag fails");
        ctx.SetChecker(SignatureCheckerMock::VALIDATION::ALWAYS_SUCCEEDS)
            .AddFlags(SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_PUBKEYTYPE)
            .SetScript()
            << SIG_64BYTES << CScriptNum(TEST_NUM) << PUBKEY_15BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallFailed(SCRIPT_ERR_DISCOURAGE_UPGRADABLE_PUBKEYTYPE)
            .CheckSignatureWasNotValidated()
            .CheckStackDepth(3);
    }

    {
        Context ctx("32byte pubkey + sig with validation failure forced");
        ctx.SetChecker(SignatureCheckerMock::VALIDATION::ALWAYS_FAILS)
            .SetScript()
            << SIG_64BYTES << CScriptNum(TEST_NUM) << PUBKEY_32BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallFailed(SCRIPT_ERR_SCHNORR_SIG)
            .CheckSignatureWasValidated()
            .CheckStackDepth(3);
    }

    {
        Context ctx("32byte pubkey + sig with validation success forced");
        ctx.SetChecker(SignatureCheckerMock::VALIDATION::ALWAYS_SUCCEEDS)
            .SetScript()
            << SIG_64BYTES << CScriptNum(TEST_NUM) << PUBKEY_32BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallSucceeded()
            .CheckSignatureWasValidated()
            .CheckRemainingValidationWeight(END_VALIDATION_WEIGHT)
            .CheckStackDepth(1)
            .CheckTOS(TEST_NUM+1);
    }

    {
        Context ctx("non32byte pubkey + empty sig with validation success forced");
        ctx.SetChecker(SignatureCheckerMock::VALIDATION::ALWAYS_SUCCEEDS)
            .SetScript()
            << SIG_EMPTY << CScriptNum(TEST_NUM) << PUBKEY_15BYTES << OP_CHECKSIGADD;
        ctx.DoTest(__LINE__)
            .CheckCallSucceeded()
            .CheckSignatureWasNotValidated()
            .CheckRemainingValidationWeight(START_VALIDATION_WEIGHT)
            .CheckStackDepth(1)
            .CheckTOS(TEST_NUM);
    }
}

BOOST_AUTO_TEST_CASE(signature_hash_schnorr_failure_cases)
{
    // As defined by BIP-341 Signature Validation Rules
    // Here we pick an acceptable SigVersion
    const SigVersion sigversion = SigVersion::TAPROOT;

    CMutableTransaction tx_to_m;
    tx_to_m.vin.push_back(CTxIn());
    const uint32_t in_pos{0};

    PrecomputedTransactionData cache;
    cache.m_bip341_taproot_ready = true;
    cache.m_spent_outputs_ready = true;

    ScriptExecutionData execdata;
    execdata.m_annex_init = true;
    execdata.m_tapleaf_hash_init = false;
    execdata.m_codeseparator_pos_init = true;

    uint256 hash_out{0};

    {
        // Check all invalid hash_type codes rejected
        const std::set<uint8_t> allowable_hash_types{ 0x00, 0x01, 0x02, 0x03, 0x81, 0x82, 0x83 };
        for (unsigned ht = 0; ht <= 255; ht++) {
            const uint8_t hash_type = static_cast<uint8_t>(ht);
            if (allowable_hash_types.find(hash_type) != allowable_hash_types.end()) continue;

            BOOST_CHECK_MESSAGE(!SignatureHashSchnorr(hash_out, execdata, tx_to_m, in_pos,
                                                      hash_type, sigversion, cache,
                                                      MissingDataBehavior::FAIL),
                                "hash_type = " << hex(hash_type) << " expected to fail");
        }
    }

    {
        // Check that if hash_type == SIGHASH_SINGLE then missing a "corresponding
        // output" fails.
        CMutableTransaction tx_to_m;
        tx_to_m.vin.push_back(CTxIn());
        tx_to_m.vin.push_back(CTxIn());
        tx_to_m.vin.push_back(CTxIn());

        uint8_t in_pos = 1;
        BOOST_CHECK_MESSAGE(!SignatureHashSchnorr(hash_out, execdata, tx_to_m,
                                                  in_pos, SIGHASH_SINGLE, sigversion, cache,
                                                  MissingDataBehavior::FAIL),
                            "SIGHASH_SINGLE with in_pos(1) > #tx_to==0 is expected to fail");

        tx_to_m.vout.push_back(CTxOut());
        in_pos = 2;
        BOOST_CHECK_MESSAGE(!SignatureHashSchnorr(hash_out, execdata, tx_to_m,
                                                  in_pos, SIGHASH_SINGLE, sigversion, cache,
                                                  MissingDataBehavior::FAIL),
                            "SIGHASH_SINGLE with in_pos(2) > #tx_to==1 is expected to fail");
    }
}

BOOST_AUTO_TEST_CASE(signature_hash_schnorr)
{
    // Our approach here will be to follow BIP-341's signature algorithm (with
    // the BIP-342 extension) doing two things at once:
    //   1) We'll set up the input arguments to `SignatureHashSchnorr` function
    //      being tested, _and_
    //   2) we'll _compute the hash of those fields ourselves_ exaxctly as
    //      it is described in BIP-341 and BIP-342.
    // Then we can compare the two.  We'll do this in a data-driven way for each
    // of the different scenarios that the algorithm supports.
    //
    // In this way this test achieves 100% _path_ coverage of `SignatureHashSchnorr`
    // (not just 100% _branch_ coverage).
    // - Sadly, this isn't shown in the `lcov` reports.  There are still a few
    //   red `-` marks left.  This is because:
    //   1. `lcov` wasn't designed to handle death tests.
    //   2. ??? Some other unknown reasons, possibly due to the instrumentation,
    //      possibly due to `lcov` limitations.  You can see by the test output
    //      (`-log_level=all`) or within a debugger that in fact _all_ branches
    //      are taken when executing all the tests in this file.

    // Here we define, and then generate, all combinations of the alternatives
    // for the parameters that vary the signature combination algorithm

    const vn_sequence<SigVersion> SigVersion_alternatives{
        {SigVersion::TAPROOT, "TAPROOT"sv},
        {SigVersion::TAPSCRIPT, "TAPSCRIPT"sv}
    };

    const vn_sequence<uint32_t> hash_type_output_alternatives{
        {SIGHASH_DEFAULT, "SIGHASH_DEFAULT"sv},
        {SIGHASH_ALL, "SIGHASH_ALL"sv},
        {SIGHASH_NONE, "SIGHASH_NONE"sv},
        {SIGHASH_SINGLE, "SIGHASH_SINGLE"sv}
    };

    const vn_sequence<uint32_t> hash_type_input_alternatives{
        {0, "N/A"sv},
        {SIGHASH_ANYONECANPAY, "SIGHASH_ANYONECANPAY"sv}
    };

    const vn_sequence<uint8_t> annex_alternatives{
        {0, "no annex"sv},
        {1, "annex present"sv}
    };

    const vn_sequence<bool> output_hash_alternatives{
        {false, "output hash missing"sv},
        {true, "output hash provided"sv}
    };

    {
        const int nAlternatives = SigVersion_alternatives.size()
                                  * hash_type_output_alternatives.size()
                                  * hash_type_input_alternatives.size()
                                  * annex_alternatives.size()
                                  * output_hash_alternatives.size()
                                  - 8 /* exclude SIGHASH_DEFAULT w/ SISHASH_ANYONECANPAY */;

        BOOST_TEST_MESSAGE("Running " << nAlternatives << "scenarios");
    }

    for (const auto& sigversion_alternative : SigVersion_alternatives)
    for (const auto& hash_type_output_alternative : hash_type_output_alternatives)
    for (const auto& hash_type_input_alternative : hash_type_input_alternatives)
    for (const auto& annex_alternative : annex_alternatives)
    for (const auto& output_hash_alternative : output_hash_alternatives)
    {
        // Exclude the invalid combination of SIGHASH_DEFAULT with SIGHASH_ANYONECANPAY
        if (hash_type_output_alternative.value == SIGHASH_DEFAULT
            && hash_type_input_alternative.value == SIGHASH_ANYONECANPAY) continue;

        // We're going to want to know which scenario it is if a check actually
        // fails ...
        std::string scenario_description;
        {
            std::ostringstream oss;
            oss << sigversion_alternative.name << ", "
                << hash_type_output_alternative.name << ", "
                << hash_type_input_alternative.name << ", "
                << annex_alternative.name << ", "
                << output_hash_alternative.name;
            scenario_description = oss.str();
        }
        BOOST_TEST_MESSAGE("Scenario: " << scenario_description);

        // Set up the scenario we're running now - these 4 variables define the scenario
        const SigVersion sigversion{sigversion_alternative.value};
        const uint8_t hash_type{static_cast<uint8_t>(hash_type_output_alternative.value
                                                   | hash_type_input_alternative.value)};
        const uint8_t annex_present{annex_alternative.value};
        const bool have_output_hash{output_hash_alternative.value};

        // Compute some helper values that depend on scenario
        const uint8_t ext_flag{sigversion == SigVersion::TAPSCRIPT};
        const uint8_t hash_input_type{static_cast<uint8_t>(hash_type & SIGHASH_INPUT_MASK)};
        const uint8_t hash_output_type{static_cast<uint8_t>((hash_type == SIGHASH_DEFAULT)
                                                             ? SIGHASH_ALL
                                                             : (hash_type & SIGHASH_OUTPUT_MASK))};
        const uint8_t spend_type = (ext_flag * 2) + annex_present;

        // Fixed values (by algorithm)
        const uint8_t epoch{0x00};
        const uint8_t key_version{0};

        // Mocked values fixed for purposes of this unit test.  This is a long
        // list of crufty things but that's because `SignatureHashSchnorr`, the
        // function begin tested, takes as arguments not just the tranaction
        // being signed (plus control data) but also some _precomputed values_
        // in two different structs: `PrecomputedTransactionData`, and
        // `ScriptExecutionData`.  On the one hand this is nice because a lot
        // of complexity of the signature algorithm doesn't have to be duplicated
        // here in this test: we can just use mocked values.  On the other hand,
        // there's a lot of icky setup to do to get all the values in the right
        // places both for our "by the book" implementation and to be set up to
        // call `SignatureHashSchnorr`.
        //
        // Try to make things simpler by at least using the same names for the
        // setup variables as for the fields in the parameter structs.

        const uint32_t in_pos{1};
        const int32_t tx_version{FillWithPattern(0x01).i32[0]};
        const uint32_t tx_lock_time{FillWithPattern(0x05).u32[0]};
        const uint256 prevouts_single_hash{FillWithPattern(0x10).u256};
        const uint256 spent_amounts_single_hash{FillWithPattern(0x18).u256};
        const uint256 spent_scripts_single_hash{FillWithPattern(0x20).u256};
        const uint256 sequences_single_hash{FillWithPattern(0x28).u256};
        const uint256 outputs_single_hash{FillWithPattern(0x30).u256};
        const uint256 output_hash{FillWithPattern(0x40).u256};
        const uint256 annex_hash{FillWithPattern(0x48).u256};
        const uint256 tapleaf_hash{FillWithPattern(0x50).u256};
        const uint32_t codeseparator_pos{FillWithPattern(0x58).u32[0]};
        const COutPoint tx_input_at_pos_prevout{FillWithPattern(0x60).u256,
                                                FillWithPattern(0x68).u32[0]};
        const uint32_t tx_input_at_pos_nsequence{FillWithPattern(0x70).u32[0]};
        CTxOut spent_output_at_pos;
        spent_output_at_pos.nValue = FillWithPattern(0x80).u64();
        spent_output_at_pos.scriptPubKey /*random script, not even valid*/
            << OP_DUP << OP_HASH160 << OP_EQUALVERIFY << OP_CHECKSIG;
        CTxOut tx_output_at_pos;
        tx_output_at_pos.nValue = FillWithPattern(0x90).u64();
        tx_output_at_pos.scriptPubKey /*random script, not even valid*/
            << OP_CHECKSIG << OP_EQUALVERIFY << OP_HASH160 << OP_DUP;

        // Now set up the arguments that are going to be passed to
        // `SignatureHashSchnorr`

        CMutableTransaction tx_to;
        tx_to.nVersion = tx_version;
        tx_to.nLockTime = tx_lock_time;
        for (uint32_t i = 0; i < in_pos+2; i++) {
            tx_to.vin.push_back(CTxIn());
            tx_to.vout.push_back(CTxOut());
        }
        tx_to.vin[in_pos].prevout = tx_input_at_pos_prevout;
        tx_to.vin[in_pos].nSequence = tx_input_at_pos_nsequence;
        tx_to.vout[in_pos] = tx_output_at_pos;

        PrecomputedTransactionData cache;
        cache.m_bip341_taproot_ready = true;
        cache.m_prevouts_single_hash = prevouts_single_hash;
        cache.m_spent_amounts_single_hash = spent_amounts_single_hash;
        cache.m_spent_scripts_single_hash = spent_scripts_single_hash;
        cache.m_sequences_single_hash = sequences_single_hash;
        cache.m_spent_outputs_ready = true;
        for (uint32_t i = 0; i < in_pos+2; i++) {
            cache.m_spent_outputs.push_back(CTxOut());
        }
        cache.m_spent_outputs[in_pos] = spent_output_at_pos;
        cache.m_outputs_single_hash = outputs_single_hash;

        ScriptExecutionData execdata;
        execdata.m_annex_init = true;
        execdata.m_annex_present = !!annex_present;
        execdata.m_annex_hash = annex_hash;
        execdata.m_output_hash.reset();
        if (have_output_hash) {
            execdata.m_output_hash = output_hash;
        }
        if (sigversion == SigVersion::TAPSCRIPT) {
            execdata.m_tapleaf_hash_init = true;
            execdata.m_tapleaf_hash = tapleaf_hash;
            execdata.m_codeseparator_pos_init = true;
            execdata.m_codeseparator_pos = codeseparator_pos;
        }

        // Now here is where we take all that data - _not_ the arguments to
        // `SignatureHashSchnorr` but all the scenario parameters, the helpers,
        // the values fixed by the algorithm, and our mocked values, and actually
        // follow the BIP-341/BIP-342 signature calculation algorithm right from
        // the specs ...

        // Start with a tagged hasher with the correct tag
        CHashWriter hasher = TaggedHash("TapSighash");

        // First byte to hash is always the "epoch", 0x00 (BIP-341, footnote 20)
        hasher << epoch;

        // Next: hash_type (1 byte)
        hasher << hash_type;

        // Next: transaction version (4 bytes)
        hasher << tx_version;

        // Next: transaction lock time (4 bytes)
        hasher << tx_lock_time;

        // Next if _not_ SIGHASH_ANYONECANPAY:
        // a) SHA256 of the serialization of all input outpoints (32 bytes)
        // b) SHA256 of the serialization of all spent output amounts (32 bytes)
        // c) SHA256 of the serialization of all spent outputs' _scriptPubKeys_
        //    serialized as script (32 bytes)
        // d) SHA256 of the serialization of all input `nSequence` (32 bytes)
        if (hash_input_type != SIGHASH_ANYONECANPAY) {
            hasher << prevouts_single_hash;
            hasher << spent_amounts_single_hash;
            hasher << spent_scripts_single_hash;
            hasher << sequences_single_hash;
        }

        // Next if _not_ SIGHASH_NONE _and not_ SIGHASH_SINGLE:
        // SHA256 of the serialization of all outputs in CTxOut format (32 bytes)
        if (hash_output_type != SIGHASH_NONE && hash_output_type != SIGHASH_SINGLE) {
            hasher << outputs_single_hash;
        }

        // Now, data about input/prevout being spent

        // The "spend_type" (1 byte) which is a function of ext_flag (above) and
        // whether there is an annex present (here: no)
        hasher << spend_type;

        // Here, if we are _not_ SIGHASH_ANYONECANPAY, we just add the index of
        // the input in the transaction input vector (4 bytes). There must be a
        // input transaction at this index but _in this scenario_ it doesn't have
        // to have any data (it is never inspected).  Same for output transactions.
        //
        // On the other hand, if we _are_ SIGHASH_ANYONECANPAY, then we add the
        // `COutPoint` of this input (36 bytes), the value of the previous
        // output spent by this input (8 bytes), the `ScriptPubKey` of the
        // previous output spent by this input (35 bytes), and the `nSequence`
        // of this input.  These values are all precomputed and made available
        // to `SignatureHashSchnorr` in the `PrecomputedTransactionData` struct.
        if (hash_input_type == SIGHASH_ANYONECANPAY) {
            hasher << tx_input_at_pos_prevout;
            hasher << spent_output_at_pos;
            hasher << tx_input_at_pos_nsequence;
        } else {
            hasher << in_pos;
        }

        // Now, if there is an "annex", add its hash (32 byte).  This is
        // precomputed and we don't actually have to have an actual annex to
        // pass in to `SignatureHashSchnorr`, nor do we have to hash it.
        if (annex_present) {
            hasher << annex_hash;
        }

        // Here, iff the hash type is `SIGHASH_SINGLE`, add the hash of the
        // corresponding transaction output (32 bytes).  The wrinkle here is that
        // (for some reason) _sometimes_ this hash is precomputed, and _sometimes_
        // it is _not_.  So `SignatureHashSchnorr` will either use it if it is
        // provided or compute it from the corresponding output itself. (For our
        // purposes in this test the output need not be valid - it just must be
        // present.)
        if (hash_output_type == SIGHASH_SINGLE) {
            if (!have_output_hash) {
                CHashWriter hasher2(SER_GETHASH, 0);
                hasher2 << tx_output_at_pos;
                hasher << hasher2.GetSHA256();
            } else {
                hasher << output_hash;
            }
        }

        // This is the TAPSCRIPT extension from BIP-342.  If the version is
        // TAPSCRIPT then add the tapleaf hash (32 bytes), the key_version (1
        // byte, fixed value of 0x00), and the "opcode position of the last
        // executed OP_CODESEPARATOR before the currently executed signature
        // opcode" (4 bytes).  The tapleaf hash and the code separator position
        // are both precomputed values.
        if (sigversion == SigVersion::TAPSCRIPT) {
            hasher << tapleaf_hash;
            hasher << key_version;
            hasher << codeseparator_pos;
        }

        // That's all that goes into the hasher for this signature
        const uint256 expected_hash_out = hasher.GetSHA256();

        // Now finally we test the actual implemented algorithm under test:
        uint256 actual_hash_out{0};
        BOOST_TEST(SignatureHashSchnorr(actual_hash_out,
                                        execdata, tx_to, in_pos,
                                        hash_type, sigversion, cache,
                                        MissingDataBehavior::FAIL),
                   "Scenario: " << scenario_description);
        BOOST_TEST(expected_hash_out == actual_hash_out,
                   "Scenario: " << scenario_description
                   << " - expected " << expected_hash_out.ToString()
                   << " == actual " << actual_hash_out.ToString());
    }
}

////////////////////////////////////////////////////////////////////////////////
// DEATH TESTS ONLY PAST THIS POINT
////////////////////////////////////////////////////////////////////////////////
//
// All the following tests are "death" tests: The test succeeds iff it causes
// a crash.  (The name comes from the popular Googletest unit test framework.)
//
// These tests use the Boost Test `execution_monitor` facility to trap signals,
// specifically: SIGABRT (which is raised by the `assert` statement - iff Linux!).
// The execution monitor will trap signals and reflect them as exceptions.  (So
// these aren't really "full" death tests à la Googletest as it is not trapping
// hard faults like calling through a null pointer.  But we don't actually need
// that so it's fine.)
//
// `assert` statement signals SIGABRT - the macro `BOOST_CHECK_SIGABRT` succeeds
// iff that SIGABRT is raised. (Could be a false positive if code signals SIGABRT
// for _some other reason than calling `assert`; also if some _other_
// `system_error` is caused ...)) (There doesn't appear to be any way to check
// the actual `assert` message to distinguish between different asserts, and the
// line number field of the exception is not set either.)
//
// N.B.: These tests are _only_ run if the OS is _not_ Windows _and_ the Thread
// Sanitizer is _not_ being used.
//
// N.B.: Apparently doesn't work with MSVC or MINGW.  Looking at Boost's
// `execution_monitor.ipp` it seems like it _should_ work: the code there
// seems to take the structured exception from the `assert` and change it to a
// `boost::execution exception`.  But, no, apparently it doesn't: the Bitcoin
// repository CI pipeline for `win64 [unit tests, no gui tests, no boost::process,
// no functional tests]` prints the assert and then aborts.  Also `win64 [native]`.
//
// N.B.: Doesn't work with the ThreadSanitizer, which doesn't like an unsafe call
// inside of the Boost Test signal handler.

#define BOOST_CHECK_SIGABRT(expr) \
{ \
    ::boost::execution_monitor exmon; \
    BOOST_CHECK_EXCEPTION( \
        exmon.vexecute([&](){(void)(expr);}), \
        boost::execution_exception, \
        [](boost::execution_exception const& ex) \
            { return ex.code() == boost::execution_exception::system_error; } \
    ); \
}

// Tests that check whether an `assert` function is hit can only run when _not_
// under Windows _and not_ under the Thread Sanitizer.
#if defined(__has_feature)
#  if __has_feature(thread_sanitizer)
#    define THREAD_SANITIZER_IN_PLAY 1
#  endif
#endif

#if defined(_MSC_VER) || defined(__MINGW32__)
#  define OS_IS_WINDOWS 1
#endif

#if !defined(THREAD_SANITIZER_IN_PLAY) && !defined(OS_IS_WINDOWS)
#  define OK_TO_TEST_ASSERT_FUNCTION 1
#endif

#if defined(OK_TO_TEST_ASSERT_FUNCTION)

BOOST_AUTO_TEST_CASE(signature_hash_schnorr_assert_cases)
{
    const SigVersion sigversion = SigVersion::TAPROOT;
    const uint8_t hash_type {SIGHASH_SINGLE};

    // Here we pass the assert
    CMutableTransaction tx_to_m;
    tx_to_m.vin.push_back(CTxIn());
    tx_to_m.vout.push_back(CTxOut());
    uint32_t in_pos {0};

    PrecomputedTransactionData cache;
    cache.m_bip341_taproot_ready = true;
    cache.m_spent_outputs_ready = true;
    cache.m_spent_outputs.push_back(CTxOut());

    ScriptExecutionData execdata;
    execdata.m_annex_init = true;
    execdata.m_annex_hash = uint256::ZERO;

    uint256 hash_out {0};

    // (Deliberate variable shadowing follows for ease in writing separate tests
    // with mainly the same setup.)
    {
        // Check that an invalid SigVersion asserts.
        const SigVersion sigversion = SigVersion::BASE;
        BOOST_CHECK_SIGABRT(!SignatureHashSchnorr(hash_out, execdata, tx_to_m,
                                                  in_pos, hash_type, sigversion, cache,
                                                  MissingDataBehavior::FAIL));
    }

    {
        // Check that in_pos must be valid w.r.t. #inputs
        const uint32_t in_pos{2};
        BOOST_CHECK_SIGABRT(!SignatureHashSchnorr(hash_out, execdata, tx_to_m,
                                                  in_pos, hash_type, sigversion, cache,
                                                  MissingDataBehavior::FAIL));
    }

    {
        // Check that annex_init must be true
        ScriptExecutionData execdata;
        execdata.m_annex_init = false;
        BOOST_CHECK_SIGABRT(!SignatureHashSchnorr(hash_out, execdata, tx_to_m,
                                                  in_pos, hash_type, sigversion, cache,
                                                  MissingDataBehavior::FAIL));
    }

    {
        // Check that tapleaf_hash_init and codeseparator_pos_init must be true
        // if version == TAPSCRIPT
        const SigVersion sigversion = SigVersion::TAPSCRIPT;
        ScriptExecutionData execdata;
        execdata.m_annex_init = true;
        execdata.m_annex_hash = uint256::ZERO;
        execdata.m_tapleaf_hash_init = false;
        execdata.m_codeseparator_pos_init = true;
        BOOST_CHECK_SIGABRT(!SignatureHashSchnorr(hash_out, execdata, tx_to_m,
                                                  in_pos, hash_type, sigversion, cache,
                                                  MissingDataBehavior::FAIL));
        execdata.m_tapleaf_hash_init = true;
        execdata.m_codeseparator_pos_init = false;
        BOOST_CHECK_SIGABRT(!SignatureHashSchnorr(hash_out, execdata, tx_to_m,
                                                  in_pos, hash_type, sigversion, cache,
                                                  MissingDataBehavior::FAIL));
    }
}

BOOST_AUTO_TEST_CASE(handle_missing_data)
{
    // `HandleMissingData` is a static free function inside of `interpreter.cpp`.
    // Easiest way to get to it is via `SignatureHashSchnorr<CMutableTransaction>`
    // which takes an explicit `MissingDataBehavior` value which is what is
    // needed to exercise `HandleMissingData`.

    // N.B.: This is somewhat fragile.  We are just finding a path through
    // `SignatureHashSchnorr` that definitely gets to `HandleMissingData`. If
    // the code in `SignatureHashSchnorr` changes for whatever reason the
    // setup code below may no longer pick out that path.

    // Here we pick an acceptable SigVersion and hash type
    const SigVersion sigversion = SigVersion::TAPROOT;
    const uint8_t hash_type {SIGHASH_DEFAULT};

    // Here we pass the assert
    CMutableTransaction tx_to_m;
    tx_to_m.vin.push_back(CTxIn());
    const CTransaction tx_to(tx_to_m);
    const uint32_t in_pos {0};

    // Here we take the `then` clause of the `if`
    PrecomputedTransactionData cache;
    cache.m_bip341_taproot_ready = false;
    cache.m_spent_outputs_ready = false;

    uint256 hash_out {0};
    ScriptExecutionData execdata;

    // `MissingDataBehavior::FAIL` simply returns false
    BOOST_CHECK(!SignatureHashSchnorr(hash_out, execdata, tx_to, in_pos,
                                      hash_type, sigversion, cache,
                                      MissingDataBehavior::FAIL));
    // Any other value for `MissingDataBehavior` triggers an `assert` function
    // which (on Linux) signals SIGABRT.
    BOOST_CHECK_SIGABRT(SignatureHashSchnorr(hash_out, execdata, tx_to, in_pos,
                                             hash_type, sigversion, cache,
                                             MissingDataBehavior::ASSERT_FAIL));
    BOOST_CHECK_SIGABRT(SignatureHashSchnorr(hash_out, execdata, tx_to, in_pos,
                                             hash_type, sigversion, cache,
                                             static_cast<MissingDataBehavior>(25)));
}

#endif

BOOST_AUTO_TEST_SUITE_END()
