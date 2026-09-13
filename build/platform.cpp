// GPL-2.0-or-later. Never invoke a host shell, including under Node tests.
#include <errno.h>
extern "C" int system(const char *command)
{
   if (!command) return 0;
   errno = ENOSYS;
   return -1;
}
