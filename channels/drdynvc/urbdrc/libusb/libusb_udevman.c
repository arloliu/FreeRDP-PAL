/**
 * FreeRDP: A Remote Desktop Protocol client.
 * RemoteFX USB Redirection
 *
 * Copyright 2012 Atrust corp.
 * Copyright 2012 Alfred Liu <alfred.liu@atruscorp.com>
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>


#include "urbdrc_types.h"
#include "urbdrc_main.h"
#include "libusb_udevice.h"

int libusb_debug;

#define BASIC_STATE_FUNC_DEFINED(_arg, _type) \
static _type udevman_get_##_arg (IUDEVMAN * idevman) \
{ \
	UDEVMAN * udevman = (UDEVMAN *) idevman; \
	return udevman->_arg; \
} \
static void udevman_set_##_arg (IUDEVMAN * idevman, _type _t) \
{ \
	UDEVMAN * udevman = (UDEVMAN *) idevman; \
	udevman->_arg = _t; \
}

#define BASIC_STATE_FUNC_REGISTER(_arg, _man) \
	_man->iface.get_##_arg = udevman_get_##_arg; \
	_man->iface.set_##_arg = udevman_set_##_arg


typedef struct _UDEVMAN UDEVMAN;
struct _UDEVMAN
{
	IUDEVMAN iface;

	IUDEVICE* idev; /* iterator device */
	IUDEVICE* head; /* head device in linked list */
	IUDEVICE* tail; /* tail device in linked list */

	uint32 defUsbDevice;
	int device_num;
	int sem_timeout;

	pthread_mutex_t devman_loading;
	sem_t   sem_urb_lock;
};
typedef UDEVMAN * PUDEVMAN;  



static void
udevman_rewind(IUDEVMAN * idevman)
{
	UDEVMAN * udevman = (UDEVMAN *) idevman; 
	udevman->idev = udevman->head;
}

static int
udevman_has_next(IUDEVMAN * idevman)
{
	UDEVMAN * udevman = (UDEVMAN *) idevman;
	if (udevman->idev == NULL)
		return 0;
	else
		return 1;
}

static IUDEVICE*
udevman_get_next(IUDEVMAN * idevman)
{
	UDEVMAN * udevman = (UDEVMAN *) idevman;
	IUDEVICE* pdev;

	pdev = udevman->idev;
	udevman->idev = (IUDEVICE*) ((UDEVICE*)udevman->idev)->next;

	return pdev;
}


static IUDEVICE*
udevman_get_udevice_by_addr(IUDEVMAN * idevman, int bus_number, int dev_number)
{
	IUDEVICE * pdev;

	idevman->rewind (idevman);
	while (idevman->has_next (idevman))
	{
		pdev = idevman->get_next (idevman);
		if (pdev->get_bus_number(pdev) == bus_number && 
			pdev->get_dev_number(pdev) == dev_number)
		{
			idevman->loading_unlock(idevman);
			return pdev;
		}
	}

	printf("udevman_get_udevice_by_addr: bus:%d dev:%d ERROR!!\n", 
		bus_number, dev_number);
	return NULL;
}



static int
udevman_register_udevice(IUDEVMAN* idevman, int bus_number, int dev_number, 
    int UsbDevice, uint16_t idVendor, uint16_t idProduct, char * option)
{
	UDEVMAN * udevman = (UDEVMAN *) idevman;
	IUDEVICE* pdev;

	if (option && strcmp(option, "new") == 0)
	{
		pdev = udev_new_by_addr(bus_number, dev_number);
		if (pdev == NULL)
			return 0;
	}
	else if (option && strcmp(option, "renew") == 0)
	{
		pdev = udev_new_by_id(idVendor, idProduct);
		if (pdev == NULL)
			return 0;
	}
	else
	{
		printf("udevman_register_udevice: function error!!");
		return 0;
	}

	pdev->set_UsbDevice(pdev, UsbDevice);


	if (udevman->head == NULL)
	{
		/* linked list is empty */
		udevman->head = pdev;
		udevman->tail = pdev;
	}
	else
	{
		/* append device to the end of the linked list */
		udevman->tail->set_p_next(udevman->tail, pdev);
		pdev->set_p_prev(pdev, udevman->tail);
		udevman->tail = pdev;
	}
	udevman->device_num += 1;

	return 1;
}


static int
udevman_unregister_udevice(IUDEVMAN * idevman, int bus_number, int dev_number)
{
	UDEVMAN * udevman = (UDEVMAN *) idevman;
	UDEVICE * pdev, * dev;
	int ret = 0, err = 0;

	dev = (UDEVICE *)udevman_get_udevice_by_addr(idevman, bus_number, dev_number);

	idevman->loading_lock(idevman);
	idevman->rewind(idevman);
	while (idevman->has_next(idevman) != 0)
	{
		pdev = (UDEVICE *)idevman->get_next(idevman);

		if (pdev == dev) /* device exists */
		{
			/* set previous device to point to next device */

			if (dev->prev != NULL)
			{
				/* unregistered device is not the head */
				pdev = dev->prev;
				pdev->next = dev->next;
			}
			else
			{
				/* unregistered device is the head, update head */
				udevman->head = (IUDEVICE*)dev->next;
			}

			/* set next device to point to previous device */

			if (dev->next != NULL)
			{
				/* unregistered device is not the tail */
				pdev = (UDEVICE *)dev->next;
				pdev->prev = dev->prev;
			}
			else
			{
				/* unregistered device is the tail, update tail */
				udevman->tail = (IUDEVICE*)dev->prev;
			}
			udevman->device_num--;
			
			break; 
		}
	}
	idevman->loading_unlock(idevman);

	if (dev)
	{
		/* reset device */
		if (err != LIBUSB_ERROR_NO_DEVICE)
		{
			ret = libusb_reset_device(dev->libusb_handle);
			if (ret<0){
				LLOGLN(10, ("libusb_reset_device: ERROR!!ret:%d\n", ret)); 
			} 
		}
		
		/* release all interface and  attach kernel driver */
		dev->iface.attach_kernel_driver((IUDEVICE*)dev);   
		
		if(dev->request_queue) zfree(dev->request_queue);
		/* free the config descriptor that send from windows */
		msusb_msconfig_free(dev->MsConfig);

		libusb_close (dev->libusb_handle);
		libusb_close (dev->hub_handle);
		
		sem_destroy(&dev->sem_id);
		/* free device info */
		if (dev->devDescriptor)
			zfree(dev->devDescriptor);
		if (dev)
			zfree(dev); 
		return 1; /* unregistration successful */
	}


	/* if we reach this point, the device wasn't found */
	return 0;
}

static void
udevman_parse_twoIDs_form_str (char *str, int *id1, int *id2, char sign)
{
	char  s1[5], *s2; 
	memset(s1, 0, sizeof(s1));

	s2 = (strchr(str, sign)) + 1; 
	strncpy(s1, str, strlen(str) - (strlen(s2)+1)); 

	*id1 = atoi(s1);
	*id2 = atoi(s2);
}



static int 
udevman_check_device_exist_by_id(IUDEVMAN * idevman, uint16 idVendor, uint16 idProduct)
{
	if (libusb_open_device_with_vid_pid (NULL, idVendor, idProduct)) 
		return 1;

	return 0;
}



static IUDEVICE*
udevman_get_udevice_by_UsbDevice_try_again(IUDEVMAN * idevman, uint32 UsbDevice)
{
	UDEVICE * pdev;
	idevman->loading_lock(idevman);
	idevman->rewind (idevman);
	while (idevman->has_next (idevman))
	{
		pdev = (UDEVICE *)idevman->get_next (idevman);
		if (pdev->UsbDevice == UsbDevice)
		{
			idevman->loading_unlock(idevman);
			return (IUDEVICE *)pdev;
		}
	}
	idevman->loading_unlock(idevman);
	return NULL;
}

static IUDEVICE*
udevman_get_udevice_by_UsbDevice(IUDEVMAN * idevman, uint32 UsbDevice)
{
	UDEVICE * pdev;
	idevman->loading_lock(idevman);
	idevman->rewind (idevman);
	while (idevman->has_next (idevman))
	{
		pdev = (UDEVICE *)idevman->get_next (idevman);
		if (pdev->UsbDevice == UsbDevice)
		{
			idevman->loading_unlock(idevman);
			return (IUDEVICE *)pdev;
		}
	}
	idevman->loading_unlock(idevman);
	/* try again */
	pdev = (UDEVICE *)idevman->get_udevice_by_UsbDevice_try_again(idevman, UsbDevice);
	if (pdev)
	{
		return (IUDEVICE *)pdev;
	}

	LLOGLN(libusb_debug, ("udevman_get_udevice_by_UsbDevice: 0x%x ERROR!!\n", 
															UsbDevice));
	return NULL;
}


static void
udevman_loading_lock(IUDEVMAN * idevman)
{
	UDEVMAN * udevman = (UDEVMAN *) idevman;
	pthread_mutex_lock(&udevman->devman_loading);
}

static void
udevman_loading_unlock(IUDEVMAN * idevman)
{
	UDEVMAN * udevman = (UDEVMAN *) idevman;
	pthread_mutex_unlock(&udevman->devman_loading);
}


static void
udevman_wait_urb(IUDEVMAN * idevman)
{
	UDEVMAN * udevman = (UDEVMAN *) idevman;
	sem_wait(&udevman->sem_urb_lock);
}


static void
udevman_push_urb(IUDEVMAN * idevman)
{
	UDEVMAN * udevman = (UDEVMAN *) idevman;
	sem_post(&udevman->sem_urb_lock);
}


BASIC_STATE_FUNC_DEFINED(defUsbDevice, uint32)
BASIC_STATE_FUNC_DEFINED(device_num, int)
BASIC_STATE_FUNC_DEFINED(sem_timeout, int)


static void
udevman_free(IUDEVMAN* idevman)
{
	UDEVMAN * udevman = (UDEVMAN *) idevman;
	pthread_mutex_destroy(&udevman->devman_loading);
	sem_destroy(&udevman->sem_urb_lock);

	libusb_exit(NULL);

	/* free udevman */
	if (udevman)
		zfree(udevman);
}


static void
udevman_load_interface(UDEVMAN * udevman)
{
	/* standard */
	udevman->iface.free = udevman_free;
	/* manage devices */
	udevman->iface.rewind = udevman_rewind;
	udevman->iface.get_next = udevman_get_next;
	udevman->iface.has_next = udevman_has_next;
	udevman->iface.register_udevice = udevman_register_udevice;
	udevman->iface.unregister_udevice = udevman_unregister_udevice;
	udevman->iface.get_udevice_by_UsbDevice = udevman_get_udevice_by_UsbDevice;
	udevman->iface.get_udevice_by_UsbDevice_try_again = 
		udevman_get_udevice_by_UsbDevice_try_again;
	/* extension */    
	udevman->iface.check_device_exist_by_id = udevman_check_device_exist_by_id;
	/* Basic state */    
	BASIC_STATE_FUNC_REGISTER(defUsbDevice, udevman);
	BASIC_STATE_FUNC_REGISTER(device_num, udevman);
	BASIC_STATE_FUNC_REGISTER(sem_timeout, udevman);
	/* control semaphore or mutex lock */
	udevman->iface.loading_lock = udevman_loading_lock;
	udevman->iface.loading_unlock = udevman_loading_unlock;
	udevman->iface.push_urb = udevman_push_urb;
	udevman->iface.wait_urb = udevman_wait_urb;
}



int FreeRDPUDEVMANEntry(PFREERDP_URBDRC_SERVICE_ENTRY_POINTS pEntryPoints)
{
	UDEVMAN* udevman;
	uint32   UsbDevice = BASE_USBDEVICE_NUM;
	int return_add = 0, bus_number, dev_number;
	RDP_PLUGIN_DATA * plugin_data = pEntryPoints->plugin_data;
	char * token;
	char * message = "none";
	char hardware_id[16];

	libusb_init(NULL);

	udevman = (PUDEVMAN)malloc(sizeof(UDEVMAN));
	udevman->device_num = 0;
	udevman->idev = NULL;
	udevman->head = NULL;
	udevman->tail = NULL;   
	udevman->sem_timeout = 0;

	pthread_mutex_init(&udevman->devman_loading, NULL);
	sem_init(&udevman->sem_urb_lock, 0, MAX_URB_REQUSET_NUM);

	/* load usb device service management */
	udevman_load_interface(udevman);

	/* set debug flag, to enable Debug message for usb data transfer*/
	if (plugin_data->data[2])
		message = (char *)plugin_data->data[2];

	if (strncmp(message, "debug", 5) == 0)
		libusb_debug = 0;
	else
		libusb_debug = 10;
		

	/* register all usb device */    
	token = strtok((char *)plugin_data->data[1], "#");
	while (token)
	{
		bus_number = 0;
		dev_number = 0;
		strcpy(hardware_id, token);
		token = strtok(NULL, "#");

		udevman_parse_twoIDs_form_str(hardware_id, &bus_number, &dev_number, '_');

		return_add = udevman->iface.register_udevice((IUDEVMAN *)udevman, 
						bus_number, dev_number, UsbDevice, 0, 0, "new");
		if (return_add)
			UsbDevice++;
	}

	udevman->defUsbDevice = UsbDevice;

	pEntryPoints->pRegisterUDEVMAN(pEntryPoints->plugin, (IUDEVMAN*) udevman);

	return 0;
}
