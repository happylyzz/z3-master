/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    warning.h

Abstract:

    Support for warning messages.

Author:

    Leonardo de Moura (leonardo) 2006-12-01.

Revision History:

--*/
#pragma once
#include<ostream>
#include<stdarg.h>

void send_warnings_to_stdout(bool flag);

void enable_warning_messages(bool flag);

void set_error_stream(std::ostream* strm);

void set_warning_stream(std::ostream* strm);

std::ostream* warning_stream();

void warning_msg(const char * msg, ...);

void format2ostream(std::ostream& out, char const* fmt, va_list args);


