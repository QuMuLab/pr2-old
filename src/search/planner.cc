#include "command_line.h"
#include "search_algorithm.h"

#include "tasks/root_task.h"
#include "task_utils/task_properties.h"
#include "utils/logging.h"
#include "utils/system.h"
#include "utils/timer.h"

#include <iostream>

#include "pr2/pr2.h"

using namespace std;
using utils::ExitCode;

int main(int argc, const char **argv) {
    try {
        utils::register_event_handlers();

        if (argc < 2) {
            utils::g_log << usage(argv[0]) << endl;
            utils::exit_with(ExitCode::SEARCH_INPUT_ERROR);
        }

        if (static_cast<string>(argv[1]) != "--help") {
            utils::g_log << "reading input..." << endl;
            tasks::read_root_task(cin);
            utils::g_log << "done reading input!" << endl;

            const AbstractTask &task = *tasks::g_root_task;
            PR2TaskProxy *task_proxy = new PR2TaskProxy(task, new PR2State(task.get_initial_state_values()));

            PR2.proxy = task_proxy;
        }

        // TODO: unit cost is not included?
        // Does this need to be a vector of strings? The conversion seems redundant
        std::vector<std::string> args(argv, argv + argc);
        bool parsed = PR2.check_options(args);
        if (!parsed) 
            throw std::invalid_argument( "Parsing Failed" );

        PR2.run_pr2();

    } catch (const utils::ExitException &e) {
        /* To ensure that all destructors are called before the program exits,
           we raise an exception in utils::exit_with() and let main() return. */
        return static_cast<int>(e.get_exitcode());
    }
}
