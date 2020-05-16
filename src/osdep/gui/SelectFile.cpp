#include <stdbool.h>
#include <string.h>
#include <sys/types.h>
#include <dirent.h>
#include <stdlib.h>
#include <stdio.h>

#include <guisan.hpp>
#include <SDL_ttf.h>
#include <guisan/sdl.hpp>
#include <guisan/sdl/sdltruetypefont.hpp>
#include "SelectorEntry.hpp"

#include "sysdeps.h"
#include "config.h"
#include "uae.h"
#include "fsdb.h"
#include "gui_handling.h"

#include "options.h"
#include "inputdevice.h"
#include "amiberry_gfx.h"

#ifdef ANDROID
#include "androidsdl_event.h"
#endif

#define DIALOG_WIDTH 520
#define DIALOG_HEIGHT 400

static bool dialogResult = false;
static bool dialogFinished = false;
static bool createNew = false;
static char workingDir[MAX_DPATH];
static const char** filefilter;
static int selectedOnStart = -1;

static gcn::Window* wndSelectFile;
static gcn::Button* cmdOK;
static gcn::Button* cmdCancel;
static gcn::ListBox* lstFiles;
static gcn::ScrollArea* scrAreaFiles;
static gcn::TextField* txtCurrent;
static gcn::Label* lblFilename;
static gcn::TextField* txtFilename;


class SelectFileListModel : public gcn::ListModel
{
	std::vector<std::string> dirs;
	std::vector<std::string> files;

public:
	SelectFileListModel(const char* path)
	{
		changeDir(path);
	}

	int getNumberOfElements() override
	{
		return int(dirs.size() + files.size());
	}

	std::string getElementAt(const int i) override
	{
		if (i >= int(dirs.size() + files.size()) || i < 0)
			return "---";
		if (i < int(dirs.size()))
			return dirs[i];
		return files[i - dirs.size()];
	}

	void changeDir(const char* path)
	{
		ReadDirectory(path, &dirs, &files);
		if (dirs.empty())
			dirs.emplace_back("..");
		FilterFiles(&files, filefilter);
	}

	[[nodiscard]] bool isDir(const unsigned int i) const
	{
		return (i < dirs.size());
	}
};

static SelectFileListModel* fileList;


class FileButtonActionListener : public gcn::ActionListener
{
public:
	void action(const gcn::ActionEvent& actionEvent) override
	{
		if (actionEvent.getSource() == cmdOK)
		{
			const auto selected_item = lstFiles->getSelected();
			if (createNew)
			{
				char tmp[MAX_DPATH];
				if (txtFilename->getText().length() <= 0)
					return;
				strncpy(tmp, workingDir, MAX_DPATH - 1);
				strncat(tmp, "/", MAX_DPATH - 1);
				strncat(tmp, txtFilename->getText().c_str(), MAX_DPATH - 2);
				if (strstr(tmp, filefilter[0]) == nullptr)
					strncat(tmp, filefilter[0], MAX_DPATH - 1);
				if (my_existsfile(tmp) == 1)
					return; // File already exists
				strncpy(workingDir, tmp, MAX_DPATH - 1);
				dialogResult = true;
			}
			else
			{
				if (fileList->isDir(selected_item))
					return; // Directory selected -> Ok not possible
				strncat(workingDir, "/", MAX_DPATH - 1);
				strncat(workingDir, fileList->getElementAt(selected_item).c_str(), MAX_DPATH - 2);
				dialogResult = true;
			}
		}
		dialogFinished = true;
	}
};

static FileButtonActionListener* fileButtonActionListener;


static void checkfoldername(char* current)
{
	char actualpath[MAX_DPATH];
	DIR* dir;

	if ((dir = opendir(current)))
	{
		fileList->changeDir(current);
		const auto ptr = realpath(current, actualpath);
		strncpy(workingDir, ptr, MAX_DPATH);
		closedir(dir);
	}
	else
		strncpy(workingDir, start_path_data, MAX_DPATH);
	txtCurrent->setText(workingDir);
}

static void checkfilename(char* current)
{
	char actfile[MAX_DPATH];
	extractFileName(current, actfile);
	for (auto i = 0; i < fileList->getNumberOfElements(); ++i)
	{
		if (!fileList->isDir(i) && !stricmp(fileList->getElementAt(i).c_str(), actfile))
		{
			lstFiles->setSelected(i);
			selectedOnStart = i;
			break;
		}
	}
}

class SelectFileActionListener : public gcn::ActionListener
{
public:
	void action(const gcn::ActionEvent& actionEvent) override
	{
		char foldername[MAX_DPATH] = "";

		const auto selected_item = lstFiles->getSelected();
		strncpy(foldername, workingDir, MAX_DPATH);
		strncat(foldername, "/", MAX_DPATH - 1);
		strncat(foldername, fileList->getElementAt(selected_item).c_str(), MAX_DPATH - 2);
		if (fileList->isDir(selected_item))
			checkfoldername(foldername);
		else if (!createNew)
		{
			strncpy(workingDir, foldername, sizeof workingDir);
			dialogResult = true;
			dialogFinished = true;
		}
	}
};

static SelectFileActionListener* selectFileActionListener;

#ifdef ANDROID
class EditFilePathActionListener : public gcn::ActionListener
{
  public:
    void action(const gcn::ActionEvent& actionEvent)
    {
       char tmp[MAX_DPATH];
       strncpy(tmp, txtCurrent->getText().c_str(), MAX_DPATH - 1);
       checkfoldername(tmp);
    }
};
static EditFilePathActionListener* editFilePathActionListener;
#endif

static void InitSelectFile(const char* title)
{
	wndSelectFile = new gcn::Window("Load");
	wndSelectFile->setSize(DIALOG_WIDTH, DIALOG_HEIGHT);
	wndSelectFile->setPosition((GUI_WIDTH - DIALOG_WIDTH) / 2, (GUI_HEIGHT - DIALOG_HEIGHT) / 2);
	wndSelectFile->setBaseColor(gui_baseCol);
	wndSelectFile->setCaption(title);
	wndSelectFile->setTitleBarHeight(TITLEBAR_HEIGHT);

	fileButtonActionListener = new FileButtonActionListener();

	cmdOK = new gcn::Button("Ok");
	cmdOK->setSize(BUTTON_WIDTH, BUTTON_HEIGHT);
	cmdOK->setPosition(DIALOG_WIDTH - DISTANCE_BORDER - 2 * BUTTON_WIDTH - DISTANCE_NEXT_X,
	                   DIALOG_HEIGHT - 2 * DISTANCE_BORDER - BUTTON_HEIGHT - 10);
	cmdOK->setBaseColor(gui_baseCol);
	cmdOK->addActionListener(fileButtonActionListener);

	cmdCancel = new gcn::Button("Cancel");
	cmdCancel->setSize(BUTTON_WIDTH, BUTTON_HEIGHT);
	cmdCancel->setPosition(DIALOG_WIDTH - DISTANCE_BORDER - BUTTON_WIDTH,
	                       DIALOG_HEIGHT - 2 * DISTANCE_BORDER - BUTTON_HEIGHT - 10);
	cmdCancel->setBaseColor(gui_baseCol);
	cmdCancel->addActionListener(fileButtonActionListener);

	txtCurrent = new gcn::TextField();
	txtCurrent->setSize(DIALOG_WIDTH - 2 * DISTANCE_BORDER - 4, TEXTFIELD_HEIGHT);
	txtCurrent->setPosition(DISTANCE_BORDER, 10);
#ifdef ANDROID
	txtCurrent->setEnabled(true);
	editFilePathActionListener =  new EditFilePathActionListener();
	txtCurrent->addActionListener(editFilePathActionListener);
#else
	txtCurrent->setEnabled(false);
#endif

	selectFileActionListener = new SelectFileActionListener();
	fileList = new SelectFileListModel(".");

	lstFiles = new gcn::ListBox(fileList);
	lstFiles->setSize(800, 252);
	lstFiles->setBaseColor(gui_baseCol);
	lstFiles->setWrappingEnabled(true);
	lstFiles->addActionListener(selectFileActionListener);

	scrAreaFiles = new gcn::ScrollArea(lstFiles);
	scrAreaFiles->setBorderSize(1);
	scrAreaFiles->setPosition(DISTANCE_BORDER, 10 + TEXTFIELD_HEIGHT + 10);
	scrAreaFiles->setSize(DIALOG_WIDTH - 2 * DISTANCE_BORDER - 4, 272);
	scrAreaFiles->setScrollbarWidth(30);
	scrAreaFiles->setBaseColor(gui_baseCol);

	if (createNew)
	{
		scrAreaFiles->setSize(DIALOG_WIDTH - 2 * DISTANCE_BORDER - 4, 272 - TEXTFIELD_HEIGHT - DISTANCE_NEXT_Y);
		lblFilename = new gcn::Label("Filename:");
		lblFilename->setSize(80, LABEL_HEIGHT);
		lblFilename->setAlignment(gcn::Graphics::LEFT);
		lblFilename->setPosition(DISTANCE_BORDER, scrAreaFiles->getY() + scrAreaFiles->getHeight() + DISTANCE_NEXT_Y);
		txtFilename = new gcn::TextField();
		txtFilename->setSize(120, TEXTFIELD_HEIGHT);
		txtFilename->setId("Filename");
		txtFilename->setPosition(lblFilename->getX() + lblFilename->getWidth() + DISTANCE_NEXT_X, lblFilename->getY());

		wndSelectFile->add(lblFilename);
		wndSelectFile->add(txtFilename);
	}

	wndSelectFile->add(cmdOK);
	wndSelectFile->add(cmdCancel);
	wndSelectFile->add(txtCurrent);
	wndSelectFile->add(scrAreaFiles);

	gui_top->add(wndSelectFile);

	lstFiles->requestFocus();
	lstFiles->setSelected(0);
	wndSelectFile->requestModalFocus();
}


static void ExitSelectFile()
{
	wndSelectFile->releaseModalFocus();
	gui_top->remove(wndSelectFile);

	delete cmdOK;
	delete cmdCancel;
	delete fileButtonActionListener;

	delete txtCurrent;
	delete lstFiles;
	delete scrAreaFiles;
	delete selectFileActionListener;
#ifdef ANDROID
  delete editFilePathActionListener;
#endif
	delete fileList;
	if (createNew)
	{
		delete lblFilename;
		delete txtFilename;
	}

	delete wndSelectFile;
}

static void navigate_right()
{
	const auto focusHdl = gui_top->_getFocusHandler();
	const auto activeWidget = focusHdl->getFocused();
	if (activeWidget == lstFiles)
		if (createNew)
			txtFilename->requestFocus();
		else
			cmdOK->requestFocus();
	else if (activeWidget == txtFilename)
		cmdOK->requestFocus();
	else if (activeWidget == cmdCancel)
		lstFiles->requestFocus();
	else if (activeWidget == cmdOK)
		cmdCancel->requestFocus();
}

static void navigate_left()
{
	const auto focusHdl = gui_top->_getFocusHandler();
	const auto activeWidget = focusHdl->getFocused();
	if (activeWidget == lstFiles)
		cmdCancel->requestFocus();
	else if (activeWidget == cmdCancel)
		cmdOK->requestFocus();
	else if (activeWidget == cmdOK)
		if (createNew)
			txtFilename->requestFocus();
		else
			lstFiles->requestFocus();
	else if (activeWidget == txtFilename)
		lstFiles->requestFocus();
}

static void SelectFileLoop()
{
	auto got_event = 0;
	SDL_Event event;
	SDL_Event touch_event;
	while (SDL_PollEvent(&event))
	{
		switch (event.type)
		{
		case SDL_KEYDOWN:
			got_event = 1;
			switch (event.key.keysym.sym)
			{
			case VK_ESCAPE:
				dialogFinished = true;
				break;

			case VK_LEFT:
				navigate_left();
				break;

			case VK_RIGHT:
				navigate_right();
				break;

			case VK_Red:
			case VK_Green:
				event.key.keysym.sym = SDLK_RETURN;
				gui_input->pushInput(event); // Fire key down
				event.type = SDL_KEYUP; // and the key up
				break;
			default:
				break;
			}
			break;

		case SDL_JOYBUTTONDOWN:
		case SDL_JOYHATMOTION:
		case SDL_JOYAXISMOTION:
			if (gui_joystick)
			{
				got_event = 1;
				const int hat = SDL_JoystickGetHat(gui_joystick, 0);

				if (SDL_JoystickGetButton(gui_joystick, host_input_buttons[0].south_button))
				{
					PushFakeKey(SDLK_RETURN);
					break;
				}
				if (SDL_JoystickGetButton(gui_joystick, host_input_buttons[0].east_button) ||
					SDL_JoystickGetButton(gui_joystick, host_input_buttons[0].start_button))
				{
					dialogFinished = true;
					break;
				}
				if (SDL_JoystickGetButton(gui_joystick, host_input_buttons[0].dpad_left) || (hat & SDL_HAT_LEFT) ||
					SDL_JoystickGetAxis(gui_joystick, host_input_buttons[0].lstick_axis_x) == -32768)
				{
					navigate_left();
					break;
				}
				if (SDL_JoystickGetButton(gui_joystick, host_input_buttons[0].dpad_right) || (hat & SDL_HAT_RIGHT)
					|| SDL_JoystickGetAxis(gui_joystick, host_input_buttons[0].lstick_axis_x) == 32767)
				{
					navigate_right();
					break;
				}
				if (SDL_JoystickGetButton(gui_joystick, host_input_buttons[0].dpad_up) || (hat & SDL_HAT_UP) ||
					SDL_JoystickGetAxis(gui_joystick, host_input_buttons[0].lstick_axis_y) == -32768)
				{
					PushFakeKey(SDLK_UP);
					break;
				}
				if (SDL_JoystickGetButton(gui_joystick, host_input_buttons[0].dpad_down) || (hat & SDL_HAT_DOWN) ||
					SDL_JoystickGetAxis(gui_joystick, host_input_buttons[0].lstick_axis_y) == 32767)
				{
					PushFakeKey(SDLK_DOWN);
					break;
				}
			}
			break;

		case SDL_FINGERDOWN:
			got_event = 1;
			memcpy(&touch_event, &event, sizeof event);
			touch_event.type = SDL_MOUSEBUTTONDOWN;
			touch_event.button.which = 0;
			touch_event.button.button = SDL_BUTTON_LEFT;
			touch_event.button.state = SDL_PRESSED;
			touch_event.button.x = float(gui_graphics->getTarget()->w) * event.tfinger.x;
			touch_event.button.y = float(gui_graphics->getTarget()->h) * event.tfinger.y;
			gui_input->pushInput(touch_event);
			break;

		case SDL_FINGERUP:
			got_event = 1;
			memcpy(&touch_event, &event, sizeof event);
			touch_event.type = SDL_MOUSEBUTTONUP;
			touch_event.button.which = 0;
			touch_event.button.button = SDL_BUTTON_LEFT;
			touch_event.button.state = SDL_RELEASED;
			touch_event.button.x = float(gui_graphics->getTarget()->w) * event.tfinger.x;
			touch_event.button.y = float(gui_graphics->getTarget()->h) * event.tfinger.y;
			gui_input->pushInput(touch_event);
			break;

		case SDL_FINGERMOTION:
			got_event = 1;
			memcpy(&touch_event, &event, sizeof event);
			touch_event.type = SDL_MOUSEMOTION;
			touch_event.motion.which = 0;
			touch_event.motion.state = 0;
			touch_event.motion.x = float(gui_graphics->getTarget()->w) * event.tfinger.x;
			touch_event.motion.y = float(gui_graphics->getTarget()->h) * event.tfinger.y;
			gui_input->pushInput(touch_event);
			break;

		case SDL_KEYUP:
		case SDL_JOYBUTTONUP:
		case SDL_MOUSEBUTTONDOWN:
		case SDL_MOUSEBUTTONUP:
		case SDL_MOUSEMOTION:
		case SDL_MOUSEWHEEL:
			got_event = 1;
			break;

		default:
			break;
		}

		//-------------------------------------------------
		// Send event to guisan-controls
		//-------------------------------------------------
#ifdef ANDROID
		androidsdl_event(event, gui_input);
#else
		gui_input->pushInput(event);
#endif	
	}

	if (got_event)
	{
		// Now we let the Gui object perform its logic.
		uae_gui->logic();
		// Now we let the Gui object draw itself.
		uae_gui->draw();
		// Finally we update the screen.
		UpdateGuiScreen();
	}
}

bool SelectFile(const char* title, char* value, const char* filter[], const bool create)
{
	dialogResult = false;
	dialogFinished = false;
	createNew = create;
	filefilter = filter;
	selectedOnStart = -1;

	InitSelectFile(title);

	extractPath(value, workingDir);
	checkfoldername(workingDir);
	checkfilename(value);

	if (selectedOnStart >= 0)
	{
		scrAreaFiles->setVerticalScrollAmount(selectedOnStart * 15);
	}
	
	// Prepare the screen once
	uae_gui->logic();
	uae_gui->draw();
	UpdateGuiScreen();

	while (!dialogFinished)
	{
		const auto start = SDL_GetPerformanceCounter();
		SelectFileLoop();
		cap_fps(start, 60);
	}

	ExitSelectFile();

	if (dialogResult)
		strncpy(value, workingDir, MAX_DPATH);

	return dialogResult;
}
